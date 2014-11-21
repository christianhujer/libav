/*
 * Microsoft Advanced Stream Format demuxer
 * Copyright (c) 2014 Alexandra Hájková
 *
 * This file is part of Libav.
 *
 * Libav is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * Libav is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Libav; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#include "libavutil/attributes.h"
#include "libavutil/avassert.h"
#include "libavutil/avstring.h"
#include "libavutil/bswap.h"
#include "libavutil/common.h"
#include "libavutil/dict.h"
#include "libavutil/internal.h"
#include "libavutil/mathematics.h"
#include "libavutil/opt.h"
#include "avformat.h"
#include "avio_internal.h"
#include "avlanguage.h"
#include "id3v2.h"
#include "internal.h"
#include "riff.h"
#include "asf.h"
#include "asfcrypt.h"

#define BMP_HEADER_SIZE 40
#define ASF_TYPE_AUDIO 0x2
#define ASF_TYPE_VIDEO 0x1
#define ASF_STREAM_NUM 0x7F
#define ASF_ERROR_CORRECTION_LENGTH_TYPE 0x60
#define ASF_PACKET_ERROR_CORRECTION_DATA_SIZE 0x2
#define ASF_NUM_OF_PAYLOADS 0x3F
#define ASF_UNICODE 0x0
#define ASF_BYTE_ARRAY 0x1
#define ASF_BOOL 0x2
#define ASF_DWORD 0x3
#define ASF_QWORD 0x4
#define ASF_WORD 0x5

typedef struct GUIDParseTable {
    const char *name;
    ff_asf_guid guid;
    int (*read_object)(AVFormatContext *, struct GUIDParseTable *);
    int is_subobject;
} GUIDParseTable;

typedef struct StreamBitrate {
    uint8_t stream_num;
    uint32_t avg_bitrate;
} StreamBitrate;

typedef struct ASFPacket {
    AVPacket *avpkt;
    int64_t dts;
    uint32_t frame_num; // ASF payloads with the same number are parts of the same frame
    int flags;
    int data_size;
    int duration;
    int size_left;
    uint8_t stream_index;
} ASFPacket;

typedef struct ASFStreamDemux {
    uint8_t stream_index; //from packet header
    int index;  // stream index in AVFormatContext, set in read_stream_properties
    int type;
    int8_t span;   // for deinterleaving
    int16_t virtual_pkt_len;
    int16_t virtual_chunk_len;
    int16_t idx_type; // index type in the Index Parameters Object
    ASFPacket *pkt;
    StreamBitrate *sb;
} ASFStreamDemux;

typedef struct {
    int data_reached;
    int seekable;
    int nb_streams;
    int stream_index; //from packet header, for the subpayload case
    int is_simple_index; // is simple index present or not 1/0
    int64_t offset; // offset of the current object
    int64_t data_offset;
    int64_t header_obj_size;
    int64_t first_packet_offset; // packet offset
    int return_subpayload;
    uint64_t sub_header_offset; // offset of subplayload header
    int64_t packet_offset; // offset of the current packet inside Data Object
    uint32_t pad_len; // padding after payload
    uint64_t preroll;
    uint32_t rep_len;
    int64_t sub_dts;
    uint8_t dts_delta; // for subpayloads
    uint16_t mult_sub_len; // total length of subpayloads array inside multiple payload
    int nb_sub; // subpayloads get from current ASF packet
    int64_t dts;
    uint32_t b_flags;    // flags with broadcast flag
    uint32_t prop_flags; // file properties object flags
    uint64_t nb_packets;      // ASF packets
    uint64_t nb_packets_left; // ASF packets, not AVPackets
    uint64_t nb_mult_left; // multiple payloads left
    int64_t unknown_offset;   // for top level header objects or subobjects whithout specified behavior
    int64_t unknown_size;
    int is_header;
    uint64_t sub_left;  // subpayloads left or not
    uint32_t packet_size;
    uint32_t packet_size_internal; // packet size stored inside ASFPacket, can be 0
    int64_t send_time;
    int duration;
    uint64_t data_size; // data object size
    // presentation time offset, equal for all streams, should be equal to send time, !100-nanosecond units
    uint64_t time_offset;
    // ASF file must not contain more than 128 streams according to the specification
    ASFStreamDemux *asf_st[128];
    enum {
        PARSE_PACKET_HEADER,
        READ_SINGLE,
        READ_SUB,
        READ_MULTI,
        READ_MULTI_SUB
    } state;
} ASFContext;

static int detect_unknown_subobject(AVFormatContext *s, int64_t offset, int64_t size);
static GUIDParseTable *find_guid(ff_asf_guid guid);

static int asf_probe(AVProbeData *pd)
{
    /* check file header */
    if (!ff_guidcmp(pd->buf, &ff_asf_header))
        return AVPROBE_SCORE_MAX;
    else
        return 0;
}

static void swap_guid(ff_asf_guid guid)
{
    FFSWAP(unsigned char, guid[0], guid[3]);
    FFSWAP(unsigned char, guid[1], guid[2]);
    FFSWAP(unsigned char, guid[4], guid[5]);
    FFSWAP(unsigned char, guid[6], guid[7]);
}

static void check_position(AVIOContext *pb,  int64_t offset, uint64_t size)
{
    if (avio_tell(pb) != offset + size)
        avio_seek(pb, offset + size, SEEK_SET);
}

static uint64_t read_obj_size(AVIOContext *pb)
{
    return avio_rl64(pb);
}

static int read_unknown(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint64_t size   = read_obj_size(pb);
    int ret;

    if (asf->is_header)
        asf->unknown_size = size;
    asf->is_header = 0;
    if (!g->is_subobject) {
        if (!(ret = strcmp(g->name, "Header Extension")))
            avio_skip(pb, 22); // skip reserved fields and Data Size
        if ((ret = detect_unknown_subobject(s, asf->unknown_offset,
            asf->unknown_size)) < 0)
            return ret;
    } else
        avio_skip(pb, size - 24);

    return 0;
}

// modified GET_STR16 from aviobuf
static int get_asf_string(AVIOContext *pb, int maxlen, char *buf, int buflen)
{
    char *q = buf;
    int ret = 0;
    if (buflen <= 0)
        return AVERROR(EINVAL);
    while (ret + 1 < maxlen) {
        uint8_t tmp;
        uint32_t ch;
        GET_UTF16(ch, (ret += 2) <= maxlen ? avio_rl16(pb) : 0, break;);
        PUT_UTF8(ch, tmp, if (q - buf < buflen - 1) *q++ = tmp;)
    }
    *q = 0;

    return ret;
}

static int read_marker(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint64_t size   = read_obj_size(pb);
    int i, nb_markers, len, ret;
    char name[1024];

    avio_rl64(pb);
    avio_rl64(pb); // skip reserved GUID
    nb_markers = avio_rl32(pb);
    avio_rl16(pb); // skip reserved field
    len = avio_rl16(pb);
    for (i = 0; i < len; i++)
        avio_r8(pb);

    for (i = 0; i < nb_markers; i++) {
        int64_t pts;

        avio_rl64(pb);
        pts = avio_rl64(pb);
        pts -= asf->preroll * 10000;
        avio_rl16(pb); // entry length
        avio_rl32(pb); // send time
        avio_rl32(pb); // flags
        len = avio_rl32(pb);

        if ((ret = avio_get_str16le(pb, len * 2, name,
                                    sizeof(name))) < len)
            avio_skip(pb, len - ret);
        avpriv_new_chapter(s, i, (AVRational) { 1, 10000000 }, pts,
                           AV_NOPTS_VALUE, name);
    }
    check_position(pb, asf->offset, size);

    return 0;
}

static int read_metadata(AVFormatContext *s, const char *title, uint16_t len,
                         unsigned char *ch, uint16_t max_len)
{
    AVIOContext *pb = s->pb;

    memset(ch, 0, max_len);
    avio_get_str16le(pb, len * sizeof(*ch), ch, len * sizeof(*ch));
    av_dict_set(&s->metadata, title, ch, 0);

    return 0;
}

static int read_value(AVFormatContext *s, int8_t *name,
                      int16_t val_len, int type)
{
    AVIOContext *pb = s->pb;
    uint8_t *value;
    int ret;

    value = av_malloc(2 * val_len);
    if (!value)
        return AVERROR(ENOMEM);
    if (type == ASF_UNICODE) {
        // get_asf_string reads UTF-16 and converts it to UTF-8 which needs longer buffer
        get_asf_string(pb, val_len, value, 2 * val_len);
        av_dict_set(&s->metadata, name, value, 0);
    } else {
        char buf[32];
        if ((ret = avio_read(pb, value, val_len)) < 0)
            return ret;
        snprintf(buf, sizeof(buf), "%s", value);
        av_dict_set(&s->metadata, name, buf, 0);
    }
    av_free(value);

    return 0;
}

static void read_generic_value(AVFormatContext *s, int8_t *name, int type)
{
    AVIOContext *pb = s->pb;
    uint64_t value;
    char buf[32];

    switch (type) {
    case ASF_BOOL:
        value = avio_rl32(pb);
        break;
    case ASF_DWORD:
        value = avio_rl32(pb);
        break;
    case ASF_QWORD:
        value = avio_rl64(pb);
        break;
    case ASF_WORD:
        value = avio_rl16(pb);
        break;
    }
    snprintf(buf, sizeof(buf), "%"PRIu64"", value);
    av_dict_set(&s->metadata, name, buf, 0);
}

static int read_ext_content(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint64_t size = read_obj_size(pb);
    int16_t nb_desc = avio_rl16(pb);
    int i;

    for (i = 0; i < nb_desc; i++) {
        int16_t name_len, type, val_len;
        char *name = NULL;

        name_len = avio_rl16(pb);
        if (name_len) {
            name = av_malloc(name_len);
            if (!name)
                return AVERROR(ENOMEM);
            avio_get_str16le(pb, name_len * sizeof(*name), name,
                             name_len);
        }
        type    = avio_rl16(pb);
        val_len = avio_rl16(pb);
        if (val_len) {
            switch (type) {
            case ASF_UNICODE:
                read_value(s, name, val_len, type);
                break;
            case ASF_BYTE_ARRAY:
                read_value(s, name, val_len, type);
                break;
            default:
                read_generic_value(s, name, type);
                break;
            }
        }
        av_free(name);
    }
    check_position(pb, asf->offset, size);

    return 0;
}

static int read_content(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    int i;
    uint16_t len[5], max_len = 0;
    const char *titles[] = { "Title", "Author", "Copyright", "Description", "Rate" };
    int8_t *ch;
    uint64_t size = read_obj_size(pb);

    for (i = 0; i < 5; i++) {
        len[i]  = avio_rl16(pb);
        max_len = FFMAX(max_len, len[i]);
    }
    ch = av_malloc(max_len * sizeof(*ch));
    if (!ch)
        return(AVERROR(ENOMEM));
    for (i = 0; i < 5; i++)
        read_metadata(s, titles[i], len[i], ch, max_len);
    av_free(ch);
    check_position(pb, asf->offset, size);

    return 0;
}

static int read_properties(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint64_t nb_packets;
    uint32_t max_packet_size;

    read_obj_size(pb);
    avio_skip(pb, 16); // skip File ID
    avio_skip(pb, 8);  // skip File size
    avio_skip(pb, 8);  // skip creation date
    nb_packets       = avio_rl64(pb);
    asf->duration    = avio_rl64(pb) / 10000; // stream duration
    avio_skip(pb, 8); //skip send duration
    asf->preroll     = avio_rl64(pb);
    asf->b_flags     = avio_rl32(pb);
    avio_skip(pb, 4); // skip minimal packet size
    max_packet_size  = avio_rl32(pb);
    avio_skip(pb, 4); //skip max_bitrate
    asf->nb_packets  = nb_packets;
    asf->packet_size = max_packet_size;

    return 0;
}

static int parse_video_info(AVIOContext *pb, AVStream *st)
{
    uint16_t size;
    unsigned int tag;

    st->codec->width  = avio_rl32(pb);
    st->codec->height = avio_rl32(pb);
    avio_skip(pb, 1); // skip reserved flags
    size = avio_rl16(pb); // size of the Format Data
    tag  = ff_get_bmp_header(pb, st);
    st->codec->codec_tag = tag;
    st->codec->codec_id  = ff_codec_get_id(ff_codec_bmp_tags, tag);

    if (size > BMP_HEADER_SIZE) {
        int ret;
        st->codec->extradata_size  = size - BMP_HEADER_SIZE;
        if (!(st->codec->extradata = av_malloc(st->codec->extradata_size)))
            return AVERROR(ENOMEM);
        if ((ret = avio_read(pb, st->codec->extradata, st->codec->extradata_size)) < 0)
            return ret;
    }
    return 0;
}

static int read_stream_properties(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint64_t size;
    uint32_t err_data_len, ts_data_len; // time specific data length
    uint16_t flags;
    int8_t *ts_data;
    ff_asf_guid stream_type;
    enum AVMediaType type;
    int ret;
    int8_t span;
    AVStream *st = avformat_new_stream(s, NULL);

    // ASF file must not contain more than 128 streams according to the specification
    if (asf->nb_streams >= 128)
        return AVERROR_INVALIDDATA;

    if (!st)
        return AVERROR(ENOMEM);
    avpriv_set_pts_info(st, 32, 1, 1000); // pts should be dword, in milliseconds
    size = read_obj_size(pb);
    ff_get_guid(pb, &stream_type);
    if (!ff_guidcmp(&stream_type, &ff_asf_audio_stream))
        type = AVMEDIA_TYPE_AUDIO;
    else if (!ff_guidcmp(&stream_type, &ff_asf_video_stream))
        type = AVMEDIA_TYPE_VIDEO;
    else if (!ff_guidcmp(&stream_type, &ff_asf_jfif_media)) {
        type                = AVMEDIA_TYPE_VIDEO;
        st->codec->codec_id = AV_CODEC_ID_MJPEG;
    } else if (!ff_guidcmp(&stream_type, &ff_asf_command_stream))
        type = AVMEDIA_TYPE_DATA;
    else if (!ff_guidcmp(&stream_type,
                         &ff_asf_ext_stream_embed_stream_header)) {
        type = AVMEDIA_TYPE_UNKNOWN;
    } else
        return AVERROR_INVALIDDATA;
    st->codec->codec_type = type;
    ff_get_guid(pb, &stream_type); // error correction type
    asf->time_offset = avio_rl64(pb);
    ts_data_len      = avio_rl32(pb);
    err_data_len     = avio_rl32(pb);
    flags            = avio_rl16(pb); // bit 15 - Encrypted Content
    if (!(asf->asf_st[asf->nb_streams] = av_mallocz(sizeof(ASFStreamDemux))))
        return AVERROR(ENOMEM);
    asf->asf_st[asf->nb_streams]->stream_index = flags & ASF_STREAM_NUM;
    asf->asf_st[asf->nb_streams]->index        = st->index;
    st->id = flags & ASF_STREAM_NUM;
    if (!(asf->asf_st[asf->nb_streams]->pkt    = av_mallocz(sizeof(ASFPacket))))
        return AVERROR(ENOMEM);
    if (!(asf->asf_st[asf->nb_streams]->pkt->avpkt = av_mallocz(sizeof(AVPacket))))
        return AVERROR(ENOMEM);
    if (!(asf->asf_st[asf->nb_streams]->sb = av_mallocz(sizeof(StreamBitrate))))
        return AVERROR(ENOMEM);
    av_init_packet(asf->asf_st[asf->nb_streams]->pkt->avpkt);
    asf->asf_st[asf->nb_streams]->pkt->data_size = 0;

    avio_skip(pb, 4); // skip reserved field
    if (ts_data_len) {
        ts_data = av_malloc(ts_data_len);
        if (!ts_data)
            return AVERROR(ENOMEM);
        switch (type) {
        case AVMEDIA_TYPE_AUDIO:
            asf->asf_st[asf->nb_streams]->type = AVMEDIA_TYPE_AUDIO;
            ret = ff_get_wav_header(pb, st->codec, ts_data_len);
            if (ret < 0) {
                av_free(ts_data);
                return ret;
            }
            break;
        case AVMEDIA_TYPE_VIDEO:
            asf->asf_st[asf->nb_streams]->type = AVMEDIA_TYPE_VIDEO;
            ret = parse_video_info(pb, st);
            if (ret < 0) {
                av_free(ts_data);
                return ret;
            }
            break;
        default:
            if ((ret = avio_read(pb, ts_data, ts_data_len)) < 0) {
                av_free(ts_data);
                return ret;
            }
            break;
        }
        av_free(ts_data);
    } else
        av_log(s, AV_LOG_WARNING, "Suspicious data found! Stream will be ignored.\n");
    if (err_data_len) {
        if (type == AVMEDIA_TYPE_AUDIO) {
            span = avio_r8(pb);
            if (span > 1) {
                asf->asf_st[asf->nb_streams]->span              = span;
                asf->asf_st[asf->nb_streams]->virtual_pkt_len   = avio_rl16(pb);
                asf->asf_st[asf->nb_streams]->virtual_chunk_len = avio_rl16(pb);
                avio_skip(pb, err_data_len - 5);
            } else
                avio_skip(pb, err_data_len);
        } else
            avio_skip(pb, err_data_len);
    }
    asf->nb_streams++;
    check_position(pb, asf->offset, size);

    return 0;
}

static int read_ext_stream_properties(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    ff_asf_guid guid;
    uint64_t size = read_obj_size(pb);
    int16_t st_name_count, nb_pay_exts;
    int i, ret;

    avio_skip(pb, 60);
    st_name_count = avio_rl16(pb);
    nb_pay_exts   = avio_rl16(pb);
    for (i = 0; i < st_name_count; i++) {
        int16_t len;
        avio_skip(pb, 2); // Language ID Index
        len = avio_rl16(pb);
        avio_skip(pb, len);
    }
    for (i = 0; i < nb_pay_exts; i++) {
        int32_t len;
        avio_skip(pb, 16); // Extension System ID
        avio_skip(pb, 2);  // Extension Data Size
        len = avio_rl32(pb);
        avio_skip(pb, len);
    }
    if ((ret = ff_get_guid(pb, &guid)) < 0)
        return ret;
    swap_guid(guid);
    g = find_guid(guid);
    if (g) {
        if ((ret = g->read_object(s, g)) < 0)
            return ret;
    }

    check_position(pb, asf->offset, size);
    return 0;
}

static int read_stream_bitrate(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    int i, j;
    uint16_t flags;
    uint8_t stream_num;
    uint32_t avg_bitrate;
    uint16_t bit_num; //number of bitrate records
    uint64_t size = read_obj_size(pb);

    bit_num = avio_rl16(pb); // number of records
    for (i = 0; i < bit_num; i++) {
        flags = avio_rl16(pb);
        stream_num  = flags & ASF_STREAM_NUM;
        avg_bitrate = avio_rl32(pb);
        for (j = 0; j < asf->nb_streams; j++) {
            if (stream_num == asf->asf_st[j]->stream_index) {
                asf->asf_st[j]->sb->stream_num  = stream_num;
                asf->asf_st[j]->sb->avg_bitrate = avg_bitrate;
            }
        }
    }

    check_position(pb, asf->offset, size);
    return 0;
}

static int read_language_list(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    int i;
    uint64_t size = read_obj_size(pb);
    int16_t nb_langs = avio_rl16(pb);

    for (i = 0; i < nb_langs; i++) {
        int8_t len, *name;
        len = avio_r8(pb);
        if (!len)
            len = 6;
        if (len) {
            len *= 2; // len is number of unicode characters - 2 bytes for each char
            name = av_malloc(len);
            if (!name) {
                return AVERROR(ENOMEM);
            }
            get_asf_string(pb, len, name, len);
            av_free(name);
        }
    }

    check_position(pb, asf->offset, size);
    return 0;
}

// returns data object offset when reading this object for the first time
static int read_data(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    int i;
    uint64_t size = asf->data_size = read_obj_size(pb);

    // skip data reading for now and read Index Object first, then return to it
    if (!asf->data_reached && pb->seekable) {
        asf->data_offset  = asf->offset;
        asf->data_reached = 1;
        avio_skip(pb, 26);
        asf->first_packet_offset = avio_tell(pb);
        avio_skip(pb, size - 24 - 26);
        return asf->offset;
    }
    if (!pb->seekable)
        asf->seekable = 0;
    for (i = 0; i < asf->nb_streams; i++)
        s->streams[i]->duration = asf->duration;
    asf->data_reached           = 0;
    asf->nb_packets_left        = asf->nb_packets;
    asf->nb_mult_left           = 0;
    asf->sub_left               = 0;
    asf->state                  = PARSE_PACKET_HEADER;
    asf->return_subpayload      = 0;
    asf->packet_size_internal   = 0;
    avio_skip(pb, 16); // skip File ID
    size = avio_rl64(pb); // Total Data Packets
    if (size != asf->nb_packets)
        av_log(s, AV_LOG_WARNING, "Number of Packets from File Properties Object is not equal to Total Data packets value! num of packets %"PRIu64" total num %"PRIu64".\n", size,
        asf->nb_packets);
    avio_skip(pb, 2); // skip reserved field

    return 0;
}

static int read_parameters(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    int16_t nb_idx_specs;
    int i, j;
    uint64_t size = read_obj_size(pb);

    avio_skip(pb, 4);
    nb_idx_specs = avio_rl16(pb);
    for (i = 0; i < nb_idx_specs; i++) {
        int16_t stream_index = avio_rl16(pb);
        for (j = 0; j < asf->nb_streams; j++) {
            if (asf->asf_st[j]->stream_index == stream_index)
                asf->asf_st[j]-> idx_type = avio_rl16(pb);
            else
                avio_skip(pb, 2);
        }
    }

    check_position(pb, asf->offset, size);
    return 0;
}

static int read_simple_index(AVFormatContext *s, GUIDParseTable *g)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    AVStream *st = NULL;
    int64_t interval; // index entry time interval in 100 ns units, usually it's 1s
    int32_t pkt_num, nb_entries, prev_pkt_num = -1;
    int i;
    uint64_t size = read_obj_size(pb);

    for (i = 0; i < asf->nb_streams; i++) {
        if (asf->asf_st[i]->type == AVMEDIA_TYPE_VIDEO) {
            st = s->streams[asf->asf_st[i]->index];
            break;
        }
    }
    if (!st) {
        avio_skip(pb, size - 24); // if there's no video stream, skip index object
        return 0;
    }
    avio_skip(pb, 16); // skip File ID
    interval = avio_rl64(pb);
    avio_skip(pb, 4);
    nb_entries = avio_rl32(pb);
    for (i = 0; i < nb_entries; i++) {
        pkt_num = avio_rl32(pb);
        avio_skip(pb, 2);
        if (prev_pkt_num != pkt_num) {
            av_add_index_entry(st, asf->first_packet_offset + asf->packet_size * pkt_num,
                               av_rescale(interval, i, 10000),
                               asf->packet_size, 0, AVINDEX_KEYFRAME);
            prev_pkt_num = pkt_num;
        }
    }
    asf->is_simple_index = 1;
    check_position(pb, asf->offset, size);

    return 0;
}

static GUIDParseTable gdef[] = {
    {"Data",                         {0x75, 0xB2, 0x26, 0x36, 0x66, 0x8E, 0x11, 0xCF, 0xA6, 0xD9, 0x00, 0xAA, 0x00, 0x62, 0xCE, 0x6C}, read_data, 1},
    {"Simple Index",                 {0x33, 0x00, 0x08, 0x90, 0xE5, 0xB1, 0x11, 0xCF, 0x89, 0xF4, 0x00, 0xA0, 0xC9, 0x03, 0x49, 0xCB}, read_simple_index, 1},
    {"Content Description",          {0x75, 0xB2, 0x26, 0x33, 0x66 ,0x8E, 0x11, 0xCF, 0xA6, 0xD9, 0x00, 0xAA, 0x00, 0x62, 0xCE, 0x6C}, read_content, 1},
    {"Extended Content Description", {0xD2, 0xD0, 0xA4, 0x40, 0xE3, 0x07, 0x11, 0xD2, 0x97, 0xF0, 0x00, 0xA0, 0xC9, 0x5e, 0xA8, 0x50}, read_ext_content, 1},
    {"Stream Bitrate Properties",    {0x7B, 0xF8, 0x75, 0xCE, 0x46, 0x8D, 0x11, 0xD1, 0x8D, 0x82, 0x00, 0x60, 0x97, 0xC9, 0xA2, 0xB2}, read_stream_bitrate, 1},
    {"File Properties",              {0x8C, 0xAB, 0xDC, 0xA1, 0xA9, 0x47, 0x11, 0xCF, 0x8E, 0xE4, 0x00, 0xC0, 0x0C, 0x20, 0x53, 0x65}, read_properties, 1},
    {"Header Extension",             {0x5F, 0xBF, 0x03, 0xB5, 0xA9, 0x2E, 0x11, 0xCF, 0x8E, 0xE3, 0x00, 0xC0, 0x0C, 0x20, 0x53, 0x65}, read_unknown, 0},
    {"Stream Properties",            {0xB7, 0xDC, 0x07, 0x91, 0xA9, 0xB7, 0x11, 0xCF, 0x8E, 0xE6, 0x00, 0xC0, 0x0C, 0x20, 0x53, 0x65}, read_stream_properties, 1},
    {"Codec List",                   {0x86, 0xD1, 0x52, 0x40, 0x31, 0x1D, 0x11, 0xD0, 0xA3, 0xA4, 0x00, 0xA0, 0xC9, 0x03, 0x48, 0xF6}, read_unknown, 1},
    {"Marker",                       {0xF4, 0x87, 0xCD, 0x01, 0xA9, 0x51, 0x11, 0xCF, 0x8E,
    0xE6, 0x00, 0xC0, 0x0C, 0x20, 0x53, 0x65}, read_marker, 1},
    {"Script Command",               {0x1E, 0xFB, 0x1A, 0x30, 0x0B, 0x62, 0x11, 0xD0, 0xA3, 0x9B, 0x00, 0xA0, 0xC9, 0x03, 0x48, 0xF6}, read_unknown, 1},
    {"Language List",                {0x7C, 0x43, 0x46, 0xa9, 0xef, 0xe0, 0x4B, 0xFC, 0xB2, 0x29, 0x39, 0x3e, 0xde, 0x41, 0x5c, 0x85}, read_language_list, 1},
    {"Padding",                      {0x18, 0x06, 0xD4, 0x74, 0xCA, 0xDF, 0x45, 0x09, 0xA4, 0xBA, 0x9A, 0xAB, 0xCB, 0x96, 0xAA, 0xE8}, read_unknown, 1},
    {"DRMv1 Header",                 {0x22, 0x11, 0xB3, 0xFB, 0xBD, 0x23, 0x11, 0xD2, 0xB4, 0xB7, 0x00, 0xA0, 0xC9, 0x55, 0xFC, 0x6E}, read_unknown, 1},
    {"DRMv2 Header",                 {0x29, 0x8A, 0xE6, 0x14, 0x26, 0x22, 0x4C, 0x17, 0xB9, 0x35, 0xDA, 0xE0, 0x7E, 0xE9, 0x28, 0x9c}, read_unknown, 1},
    {"Index",                        {0xD6, 0xE2, 0x29, 0xD3, 0x35, 0xDA, 0x11, 0xD1, 0x90, 0x34, 0x00, 0xA0, 0xC9, 0x03, 0x49, 0xBE}, read_unknown, 1},
    {"Media Object Index",           {0xFE, 0xB1, 0x03, 0xF8, 0x12, 0xAD, 0x4C, 0x64, 0x84, 0x0F, 0x2A, 0x1D, 0x2F, 0x7A, 0xD4, 0x8C}, read_unknown, 1},
    {"Timecode Index",               {0x3C, 0xB7, 0x3F, 0xD0, 0x0C, 0x4A, 0x48, 0x03, 0x95, 0x3D, 0xED, 0xF7, 0xB6, 0x22, 0x8F, 0x0C}, read_unknown, 0},
    {"Bitrate_Mutual_Exclusion",     {0xD6, 0xE2, 0x29, 0xDC, 0x35, 0xDA, 0x11, 0xD1, 0x90, 0x34, 0x00, 0xA0, 0xC9, 0x03, 0x49, 0xBE}, read_unknown, 1},
    {"Error Correction",             {0x75, 0xB2, 0x26, 0x35, 0x66, 0x8E, 0x11, 0xCF, 0xA6, 0xD9, 0x00, 0xAA, 0x00, 0x62, 0xCE, 0x6C}, read_unknown, 1},
    {"Content Branding",             {0x22, 0x11, 0xB3, 0xFA, 0xBD, 0x23, 0x11, 0xD2, 0xB4, 0xB7, 0x00, 0xA0, 0xC9, 0x55, 0xFC, 0x6E}, read_unknown, 1},
    {"Content Encryption",           {0x22, 0x11, 0xB3, 0xFB, 0xBD, 0x23, 0x11, 0xD2, 0xB4, 0xB7, 0x00, 0xA0, 0xC9, 0x55, 0xFC, 0x6E}, read_unknown, 1},
    {"Extended Content Encryption",  {0x29, 0x8A, 0xE6, 0x14, 0x26, 0x22, 0x4C, 0x17, 0xB9, 0x35, 0xDA, 0xE0, 0x7E, 0xE9, 0x28, 0x9C}, read_unknown, 1},
    {"Digital Signature",            {0x22, 0x11, 0xB3, 0xFC, 0xBD, 0x23, 0x11, 0xD2, 0xB4, 0xB7, 0x00, 0xA0, 0xC9, 0x55, 0xFC, 0x6E}, read_unknown, 1},
    {"Extended Stream Properties",   {0x14, 0xE6, 0xA5, 0xCB, 0xC6, 0x72, 0x43, 0x32, 0x83, 0x99, 0xA9, 0x69, 0x52, 0x06, 0x5B, 0x5A}, read_ext_stream_properties, 1},
    {"Advanced Mutual Exclusion",    {0xA0, 0x86, 0x49, 0xCF, 0x47, 0x75, 0x46, 0x70, 0x8A, 0x16, 0x6E, 0x35, 0x35, 0x75, 0x66, 0xCD}, read_unknown, 1},
    {"Group Mutual Exclusion",       {0xD1, 0x46, 0x5A, 0x40, 0x5A, 0x79, 0x43, 0x38, 0xB7, 0x1B, 0xE3, 0x6B, 0x8F, 0xD6, 0xC2, 0x49}, read_unknown, 1},
    {"Stream Prioritization",        {0xD4, 0xFE, 0xD1, 0x5B, 0x88, 0xD3, 0x45, 0x4F, 0x81, 0xF0, 0xED, 0x5C, 0x45, 0x99, 0x9E, 0x24}, read_unknown, 1},
    {"Bandwidth Sharing Object",     {0xA6, 0x96, 0x09, 0xE6, 0x51, 0x7B, 0x11, 0xD2, 0xB6, 0xAF, 0x00, 0xC0, 0x4F, 0xD9, 0x08, 0xE9}, read_unknown, 1},
    {"Metadata",                     {0xC5, 0xF8, 0xCB, 0xEA, 0x5B, 0xAF, 0x48, 0x77, 0x84, 0x67, 0xAA, 0x8C, 0x44, 0xFA, 0x4C, 0xCA}, read_unknown, 1},
    {"Audio Spread",                 {0xBF, 0xC3, 0xCD, 0x50, 0x61, 0x8F, 0x11, 0xCF, 0x8B, 0xB2, 0x00, 0xAA, 0x00, 0xB4, 0xE2, 0x20}, read_unknown, 1},
    {"Index Parameters",             {0xD6, 0xE2, 0x29, 0xDF, 0x35, 0xDA, 0x11, 0xD1, 0x90, 0x34, 0x00, 0xA0, 0xC9, 0x03, 0x49, 0xBE}, read_parameters, 1},
    {"Content Encryption System Windows Media DRM Network Devices",
                                     {0x7A, 0x07, 0x9B, 0xB6, 0xDA, 0XA4, 0x4e, 0x12, 0xA5, 0xCA, 0x91, 0xD3, 0x8D, 0xC1, 0x1A, 0x8D}, read_unknown, 1},
    {"Mutex Language",               {0xD6, 0xE2, 0x2A, 0x00, 0x25, 0xDA, 0x11, 0xD1, 0x90, 0x34, 0x00, 0xA0, 0xC9, 0x03, 0x49, 0xBE}, read_unknown, 1},
    {"Mutex Bitrate",                {0xD6, 0xE2, 0x2A, 0x01, 0x25, 0xDA, 0x11, 0xD1, 0x90, 0x34, 0x00, 0xA0, 0xC9, 0x03, 0x49, 0xBE}, read_unknown, 1},
    {"Mutex Unknown",                {0xD6, 0xE2, 0x2A, 0x02, 0x25, 0xDA, 0x11, 0xD1, 0x90, 0x34, 0x00, 0xA0, 0xC9, 0x03, 0x49, 0xBE}, read_unknown, 1},
    {"Bandwith Sharing Exclusive",   {0xAF, 0x60, 0x60, 0xAA, 0x51, 0x97, 0x11, 0xD2, 0xB6, 0xAF, 0x00, 0xC0, 0x4F, 0xD9, 0x08, 0xE9}, read_unknown, 1},
    {"Bandwith Sharing Partial",     {0xAF, 0x60, 0x60, 0xAB, 0x51, 0x97, 0x11, 0xD2, 0xB6, 0xAF, 0x00, 0xC0, 0x4F, 0xD9, 0x08, 0xE9}, read_unknown, 1},
    {"Payload Extension System Timecode", {0x39, 0x95, 0x95, 0xEC, 0x86, 0x67, 0x4E, 0x2D, 0x8F, 0xDB, 0x98, 0x81, 0x4C, 0xE7, 0x6C, 0x1E}, read_unknown, 1},
    {"Payload Extension System File Name", {0xE1, 0x65, 0xEC, 0x0E, 0x19, 0xED, 0x45, 0xD7, 0xB4, 0xA7, 0x25, 0xCB, 0xD1, 0xE2, 0x8E, 0x9B}, read_unknown, 1},
    {"Payload Extension System Content Type", {0xD5, 0x90, 0xDC, 0x20, 0x07, 0xBC, 0x43, 0x6C, 0x9C, 0xF7, 0xF3, 0xBB, 0xFB, 0xF1, 0xA4, 0xDC}, read_unknown, 1},
    {"Payload Extension System Pixel Aspect Ratio", {0x1, 0x1E, 0xE5, 0x54, 0xF9, 0xEA, 0x4B, 0xC8, 0x82, 0x1A, 0x37, 0x6B, 0x74, 0xE4, 0xC4, 0xB8}, read_unknown, 1},
    {"Payload Extension System Sample Duration", {0xC6, 0xBD, 0x94, 0x50, 0x86, 0x7F, 0x49, 0x07, 0x83, 0xA3, 0xC7, 0x79, 0x21, 0xB7, 0x33, 0xAD}, read_unknown, 1},
    {"Payload Extension System Encryption Sample ID", {0x66, 0x98, 0xB8, 0x4E, 0x0A, 0xFA, 0x43, 0x30, 0xAE, 0xB2, 0x1C, 0x0A, 0x98, 0xD7, 0xA4, 0x4D}, read_unknown, 1},
    {"Payload Extension System Degradable JPEG", {0x00, 0xE1, 0xAF, 0x06, 0x7B, 0xEC, 0x11, 0xD1, 0xA5, 0x82, 0x00, 0xC0, 0x4F, 0xC2, 0x9C, 0xFB}, read_unknown, 1},
};

#define read_length(flag, name, len)        \
    do {                                    \
        if ((flag) == name ## IS_BYTE)      \
             len = avio_r8(pb);             \
        else if ((flag) == name ## IS_WORD) \
             len = avio_rl16(pb);           \
        else if ((flag) == name ## IS_DWORD)\
             len = avio_rl32(pb);           \
        else                                \
             len = 0;                       \
    } while(0)

static int read_subpayload(AVFormatContext *s, AVPacket *pkt, int is_header)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint8_t sub_len;
    int ret, i;

    if (is_header) {
        asf->dts_delta = avio_r8(pb);
        if (asf->nb_mult_left) {
            asf->mult_sub_len = avio_rl16(pb); // total
        }
        asf->sub_header_offset = avio_tell(pb);
        asf->nb_sub = 0;
        asf->sub_left = 1;
    }
    sub_len = avio_r8(pb);
    if ((ret = av_get_packet(pb, pkt, sub_len)) < 0) // each subpayload is entire frame
        return ret;
    for (i = 0; i < asf->nb_streams; i++) {
        if (asf->stream_index == asf->asf_st[i]->stream_index) {
            pkt->stream_index  = asf->asf_st[i]->index;
            break;
        }
    }
    asf->return_subpayload = 1;
    if (!sub_len)
        asf->return_subpayload = 0;

    if (sub_len)
        asf->nb_sub++;
    pkt->dts = asf->sub_dts + (asf->nb_sub - 1) * asf->dts_delta - asf->preroll;
    if (asf->nb_mult_left && (avio_tell(pb) >= (asf->sub_header_offset + asf->mult_sub_len))) {
        asf->sub_left = 0;
        asf->nb_mult_left--;
    }
    if (avio_tell(pb) >= (asf->packet_offset + asf->packet_size - asf->pad_len)) {
        asf->sub_left = 0;
        if (!asf->nb_mult_left) {
            avio_skip(pb, asf->pad_len);
            asf->nb_packets_left--;
            if (avio_tell(pb) != asf->packet_offset + asf->packet_size) {
                av_log(s, AV_LOG_WARNING, "Position %"PRId64" wrong, should be %"PRId64"\n",
                       avio_tell(pb), asf->packet_offset + asf->packet_size);
                avio_seek(pb, asf->packet_offset + asf->packet_size, SEEK_SET);
            }
        }
    }

    return 0;
}

static void reset_packet(ASFPacket *asf_pkt)
{
    asf_pkt->size_left = 0;
    asf_pkt->data_size = 0;
    asf_pkt->duration  = 0;
    asf_pkt->flags     = 0;
    asf_pkt->dts       = 0;
    asf_pkt->duration  = 0;
    av_free_packet(asf_pkt->avpkt);
    av_init_packet(asf_pkt->avpkt);
}

static int read_multiple_payload(AVFormatContext *s, AVPacket *pkt, ASFPacket *asf_pkt)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint16_t pay_len;
    unsigned char *p;
    int ret;
    int skip = 0;

    // if replicated lenght is 1, subpayloads are present
    if (asf->rep_len == 1) {
        asf->sub_left = 1;
        asf->state = READ_MULTI_SUB;
        pkt->flags = asf_pkt->flags;
        if ((ret = read_subpayload(s, pkt, 1)) < 0)
            return ret;
    } else {
        if (!asf_pkt->data_size) {
            asf_pkt->data_size = asf_pkt->size_left = avio_rl32(pb); // read media object size
            if (asf_pkt->data_size <= 0)
                return AVERROR_EOF;
            if ((ret = av_new_packet(asf_pkt->avpkt, asf_pkt->data_size)) < 0)
                return ret;
        } else
            avio_skip(pb, 4); // reading of media object size is already done
        asf_pkt->dts = avio_rl32(pb); // read presentation time
        if ((asf->rep_len - 8) > 0)
            avio_skip(pb, asf->rep_len - 8); // skip replicated data
        pay_len = avio_rl16(pb); // payload length should be WORD
        if (pay_len > asf->packet_size) {
            av_log(s, AV_LOG_ERROR, "Error: invalid data packet size, pay_len %"PRIu16", asf->packet_size %"PRIu32", offset %"PRId64".\n",
            pay_len, asf->packet_size, avio_tell(pb));
            return AVERROR_INVALIDDATA;
        }
        p = asf_pkt->avpkt->data + asf_pkt->data_size - asf_pkt->size_left;
        if ((p + pay_len) > (asf_pkt->avpkt->data + asf_pkt->data_size)) {
            av_log(s, AV_LOG_ERROR, "Error: invalid buffer size, pay_len %d, data size left %d.\n",
            pay_len, asf_pkt->size_left);
            skip = pay_len - asf_pkt->size_left;
            pay_len = asf_pkt->size_left;
        }
        if ((ret = avio_read(pb, p, pay_len)) < 0)
            return ret;
        avio_skip(pb, skip);
        asf_pkt->size_left -= pay_len;
        asf->nb_mult_left--;
    }

    return 0;
}

static int read_single_payload(AVFormatContext *s, AVPacket *pkt, ASFPacket *asf_pkt)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    int64_t  offset;
    uint64_t size;
    unsigned char *p;
    int ret;

    if (!asf_pkt->data_size) {
        asf_pkt->data_size = asf_pkt->size_left = avio_rl32(pb); // read media object size
        if (asf_pkt->data_size <= 0)
            return AVERROR_EOF;
        if ((ret = av_new_packet(asf_pkt->avpkt, asf_pkt->data_size)) < 0)
            return ret;
    } else
        avio_skip(pb, 4); // skip media object size
    asf_pkt->dts = avio_rl32(pb); // read presentation time
    if ((asf->rep_len - 8) > 0)
        avio_skip(pb, asf->rep_len - 8); // skip replicated data
    offset = avio_tell(pb);

    // size of the payload - size of the packet without header and padding
    if (asf->packet_size_internal)
        size = asf->packet_size_internal - offset + asf->packet_offset - asf->pad_len;
    else
        size = asf->packet_size - offset + asf->packet_offset - asf->pad_len;
    if (size > asf->packet_size) {
        av_log(s, AV_LOG_ERROR, "Error: invalid data packet size, offset %"PRId64".\n",
        avio_tell(pb));
        return AVERROR_INVALIDDATA;
    }
    p = asf_pkt->avpkt->data + asf_pkt->data_size - asf_pkt->size_left;
    if (asf_pkt->size_left > size)
        asf_pkt->size_left -= size;
    else
        asf_pkt->size_left = 0;
    if ((ret = avio_read(pb, p, size)) < 0)
        return ret;
    if (asf->packet_size_internal)
        avio_skip(pb, asf->packet_size - asf->packet_size_internal);
    avio_skip(pb, asf->pad_len); // skip padding

    return 0;
}

static int read_payload(AVFormatContext *s, AVPacket *pkt)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint8_t stream_num;
    uint32_t off_len, media_len;
    int ret, i;
    ASFPacket *asf_pkt = NULL;

    if (!asf->sub_left) {
        stream_num = avio_r8(pb);
        asf->stream_index = stream_num & ASF_STREAM_NUM;
        for (i = 0; i < asf->nb_streams; i++) {
            if (asf->stream_index == asf->asf_st[i]->stream_index) {
                asf_pkt = asf->asf_st[i]->pkt;
                asf_pkt->stream_index = asf->asf_st[i]->index;
                asf_pkt->dts = asf->dts;
                break;
            }
        }
        if (!asf_pkt)
            return AVERROR_INVALIDDATA;
        if (stream_num >> 7)
            asf_pkt->flags |= AV_PKT_FLAG_KEY;
        read_length(asf->prop_flags & ASF_PL_MASK_MEDIA_OBJECT_NUMBER_LENGTH_FIELD_SIZE,
                    ASF_PL_FLAG_MEDIA_OBJECT_NUMBER_LENGTH_FIELD_, media_len);
        read_length(asf->prop_flags & ASF_PL_MASK_OFFSET_INTO_MEDIA_OBJECT_LENGTH_FIELD_SIZE,
                    ASF_PL_FLAG_OFFSET_INTO_MEDIA_OBJECT_LENGTH_FIELD_, off_len);
        read_length(asf->prop_flags & ASF_PL_MASK_REPLICATED_DATA_LENGTH_FIELD_SIZE,
                    ASF_PL_FLAG_REPLICATED_DATA_LENGTH_FIELD_, asf->rep_len);
        if (asf_pkt) {
            if (asf_pkt->size_left && (asf_pkt->frame_num != media_len)) {
                av_log(s, AV_LOG_WARNING, "Unfinished frame will be ignored\n");
                reset_packet(asf_pkt);
            }
            asf_pkt->frame_num = media_len;
        }
        asf->sub_dts = off_len;
        if (asf->nb_mult_left) {
            if ((ret = read_multiple_payload(s, pkt, asf_pkt)) < 0)
                return ret;
        } else if (asf->rep_len == 1) {
            asf->sub_left = 1;
            asf->state    = READ_SUB;
            pkt->flags = asf_pkt->flags;
            if ((ret = read_subpayload(s, pkt, 1)) < 0)
                return ret;
        } else {
            if ((ret = read_single_payload(s, pkt, asf_pkt)) < 0)
                return ret;
        }
    } else {
        for (i = 0; i <= asf->nb_streams; i++) {
            if (asf->stream_index == asf->asf_st[i]->stream_index) {
                asf_pkt = asf->asf_st[i]->pkt;
                break;
            }
        }
        if (!asf_pkt)
            return AVERROR_INVALIDDATA;
        pkt->flags         = asf_pkt->flags;
        pkt->dts           = asf_pkt->dts;
        pkt->stream_index  = asf->asf_st[i]->index;
        if ((ret = read_subpayload(s, pkt, 0)) < 0) // read subpayload without its header
            return ret;
    }

    return 0;
}

static int read_packet_header(AVFormatContext *s)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    uint64_t size;
    uint32_t av_unused seq;
    unsigned char error_flags, len_flags, pay_flags;

    asf->packet_offset = avio_tell(pb);
    error_flags = avio_r8(pb); // read Error Correction Flags
    if (error_flags & ASF_PACKET_FLAG_ERROR_CORRECTION_PRESENT)
        if (!(error_flags & ASF_ERROR_CORRECTION_LENGTH_TYPE)) {
            size = error_flags & ASF_PACKET_ERROR_CORRECTION_DATA_SIZE;
            avio_skip(pb, size);
        }
    len_flags = avio_r8(pb);
    asf->prop_flags = avio_r8(pb);
    read_length(len_flags & ASF_PPI_MASK_PACKET_LENGTH_FIELD_SIZE,
                ASF_PPI_FLAG_PACKET_LENGTH_FIELD_, asf->packet_size_internal);
    read_length(len_flags & ASF_PPI_MASK_SEQUENCE_FIELD_SIZE,
                ASF_PPI_FLAG_SEQUENCE_FIELD_, seq);
    read_length(len_flags & ASF_PPI_MASK_PADDING_LENGTH_FIELD_SIZE,
                ASF_PPI_FLAG_PADDING_LENGTH_FIELD_, asf->pad_len );
    asf->send_time = avio_rl32(pb); // send time
    avio_skip(pb, 2); // skip duration
    if (len_flags & ASF_PPI_FLAG_MULTIPLE_PAYLOADS_PRESENT) { // Multiple Payloads present
        pay_flags = avio_r8(pb);
        asf->nb_mult_left = (pay_flags & ASF_NUM_OF_PAYLOADS);
    }

    return 0;
}

static int do_deinterleaving(AVFormatContext *s, ASFPacket *asf_pkt, int i)
{
    ASFContext *asf = s->priv_data;
    int pos = 0, j, l, ret;
    unsigned char *p = asf_pkt->avpkt->data;
    int16_t pkt_len = asf->asf_st[i]->virtual_pkt_len;
    int16_t chunk_len = asf->asf_st[i]->virtual_chunk_len;
    int nchunks = pkt_len/chunk_len;
    AVPacket *buf = av_mallocz(sizeof(AVPacket));

    if (!buf)
        return AVERROR(ENOMEM);
    if ((ret = av_new_packet(buf, asf_pkt->data_size)) < 0) {
        av_free(buf);
        return ret;
    }
    while (asf_pkt->data_size >= asf->asf_st[i]->span * pkt_len + pos) {
        for (l = 0; l < pkt_len; l++) {
            if (pos >= asf_pkt->data_size)
                break;
            for (j = 0; j < asf->asf_st[i]->span; j++) {
                memcpy(buf->data + pos,
                       p + (j * nchunks + l) * chunk_len,
                       chunk_len);
                pos += chunk_len;
            }
        }
        p += asf->asf_st[i]->span * pkt_len;
        if (p > asf_pkt->avpkt->data + asf_pkt->data_size)
            break;
    }
    av_free_packet(asf_pkt->avpkt);
    av_free(asf_pkt->avpkt);
    asf_pkt->avpkt = buf;

    return 0;
}

static int asf_read_packet(AVFormatContext *s, AVPacket *pkt)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    int ret, i;

    if ((avio_tell(pb) >= asf->data_offset + asf->data_size) && !(asf->b_flags & 1))
        return AVERROR_EOF;
    while (!pb->eof_reached) {
        if (asf->state == PARSE_PACKET_HEADER) {
            read_packet_header(s);
            if (!asf->nb_mult_left)
                asf->state = READ_SINGLE;
            else
                asf->state = READ_MULTI;
        }
        switch (asf->state) {
        case READ_SINGLE:
            if ((ret = read_payload(s, pkt)) < 0)
                return ret;
            if (!asf->sub_left)
                asf->state = PARSE_PACKET_HEADER;
            break;
        case READ_SUB:
            if ((ret = read_payload(s, pkt)) < 0)
                return ret;
            if (!asf->sub_left) {
                asf->state = PARSE_PACKET_HEADER;
            }
            break;
        case READ_MULTI_SUB:
            if ((ret = read_payload(s, pkt)) < 0)
                return ret;
            if (!asf->sub_left && !asf->nb_mult_left) {
                asf->state = PARSE_PACKET_HEADER;
                if (!asf->return_subpayload) {
                    avio_skip(pb, asf->pad_len); // skip padding
                }
                if (asf->packet_offset + asf->packet_size > avio_tell(pb)) {
                    avio_seek(pb, asf->packet_offset + asf->packet_size, SEEK_SET);
                }
            } else if (!asf->sub_left)
                asf->state = READ_MULTI;
            break;
        case READ_MULTI:
            if ((ret = read_payload(s, pkt)) < 0)
                return ret;
            if (!asf->nb_mult_left) {
                asf->state = PARSE_PACKET_HEADER;
                if (!asf->return_subpayload) {
                    avio_skip(pb, asf->pad_len); // skip padding
                }
                if (asf->packet_offset + asf->packet_size > avio_tell(pb))
                    avio_seek(pb, asf->packet_offset + asf->packet_size, SEEK_SET);
            }
            break;
        }
        if (asf->return_subpayload) {
            asf->return_subpayload = 0;
            return 0;
        }
        for (i = 0; i < s->nb_streams; i++) {
            ASFPacket *asf_pkt = asf->asf_st[i]->pkt;
            if (!asf_pkt->size_left && asf_pkt->data_size) {
                if (asf->asf_st[i]->span > 1 && asf->asf_st[i]->type == AVMEDIA_TYPE_AUDIO)
                    if ((ret = do_deinterleaving(s, asf_pkt, i)) < 0)
                        return ret;
                av_packet_move_ref(pkt, asf_pkt->avpkt);
                pkt->stream_index  = asf->asf_st[i]->index;
                pkt->flags         = asf_pkt->flags;
                pkt->dts           = asf_pkt->dts - asf->preroll;
                asf_pkt->data_size = 0;
                asf_pkt->frame_num = 0;
                return 0;
            }
        }
    }

    if (pb->eof_reached)
        return AVERROR_EOF;

    return 0;
}

static int asf_read_close(AVFormatContext *s)
{
    ASFContext *asf = s->priv_data;
    int i;

    for (i = 0; i < asf->nb_streams; i++) {
        av_free_packet(asf->asf_st[i]->pkt->avpkt);
        av_free(asf->asf_st[i]->pkt->avpkt);
        av_free(asf->asf_st[i]->pkt);
        av_free(asf->asf_st[i]->sb);
        av_free(asf->asf_st[i]);
    }

    return 0;
}

static void reset_packet_state(AVFormatContext *s)
{
    ASFContext *asf    = s->priv_data;
    int i;

    asf->state             = PARSE_PACKET_HEADER;
    asf->offset            = 0;
    asf->return_subpayload = 0;
    asf->sub_left          = 0;
    asf->sub_header_offset = 0;
    asf->packet_offset     = asf->first_packet_offset;
    asf->pad_len           = 0;
    asf->rep_len           = 0;
    asf->dts_delta         = 0;
    asf->mult_sub_len      = 0;
    asf->nb_mult_left      = 0;
    asf->nb_sub            = 0;
    asf->prop_flags        = 0;
    asf->sub_dts           = 0;
    asf->dts               = 0;
    for (i = 0; i < asf->nb_streams; i++) {
        ASFPacket *pkt = asf->asf_st[i]->pkt;
        pkt->size_left = 0;
        pkt->data_size = 0;
        pkt->duration  = 0;
        pkt->flags     = 0;
        pkt->dts       = 0;
        pkt->duration  = 0;
        av_free_packet(pkt->avpkt);
        av_init_packet(pkt->avpkt);
    }
}

static int64_t asf_read_timestamp(AVFormatContext *s, int stream_index,
                                  int64_t *pos, int64_t pos_limit)
{
    ASFContext *asf = s->priv_data;
    AVPacket *pkt = av_mallocz(sizeof(*pkt));
    int64_t pkt_pos = *pos, pkt_offset, dts = 0, data_end;
    int n;

    if (!pkt)
        return AVERROR(ENOMEM);
    data_end = asf->data_offset + asf->data_size;
    if (pkt_pos > (asf->first_packet_offset + asf->packet_size) &&
        pkt_pos < data_end) {
        n = (pkt_pos - asf->first_packet_offset + asf->packet_size - 1) / asf->packet_size;
        pkt_pos = ((pkt_pos - asf->first_packet_offset) % asf->packet_size) ?
            asf->first_packet_offset + (n + 1) * asf->packet_size :
            asf->first_packet_offset +  n      * asf->packet_size;
    } else if (pkt_pos < (asf->first_packet_offset + asf->packet_size))
        pkt_pos = asf->first_packet_offset;
    else
        pkt_pos = data_end - asf->packet_size; // last packet offset
    avio_seek(s->pb, pkt_pos, SEEK_SET);
    pkt_offset = pkt_pos;

    reset_packet_state(s);
    while (avio_tell(s->pb) < data_end) {
        int i, ret, st_found;

        av_init_packet(pkt);
        pkt_offset = avio_tell(s->pb);
        if ((ret = asf_read_packet(s, pkt)) < 0) {
            dts = AV_NOPTS_VALUE;
            return ret;
        }
        // ASFPacket may contain fragments of packets belonging to different streams,
        // pkt_offset is the offset of the first fragment within it
        if (pkt_offset >= (pkt_pos + asf->packet_size))
            pkt_pos += asf->packet_size;
        for (i = 0; i < asf->nb_streams; i++) {
            ASFStreamDemux *st = asf->asf_st[i];

            st_found = 0;
            if (pkt->flags & AV_PKT_FLAG_KEY) {
                dts = pkt->dts;
                if (dts) {
                    av_add_index_entry(s->streams[pkt->stream_index], pkt_pos, dts,
                                       pkt->size, 0, AVINDEX_KEYFRAME);
                    if (stream_index == st->index) {
                        st_found = 1;
                        break;
                    }
                }
           }
        }
        if (st_found)
            break;
        av_free_packet(pkt);
    }
    *pos = pkt_pos;

    av_free(pkt);
    if (!dts)
        dts = AV_NOPTS_VALUE;
    return dts;
}

static int asf_read_seek(AVFormatContext *s, int stream_index, int64_t timestamp, int flags)
{
    ASFContext *asf = s->priv_data;
    int idx;

    if (!timestamp) {
        reset_packet_state(s);
        avio_seek(s->pb, asf->first_packet_offset, SEEK_SET);
        return 0;
    }
    if (s->streams[stream_index]->nb_index_entries && asf->is_simple_index) {
        idx = av_index_search_timestamp(s->streams[stream_index], timestamp, flags);
        if (idx < 0 || idx > s->streams[stream_index]->nb_index_entries) {
            return AVERROR_INVALIDDATA;
        }
        avio_seek(s->pb, s->streams[stream_index]->index_entries[idx].pos, SEEK_SET);
    } else {
        if (ff_seek_frame_binary(s, stream_index, timestamp, flags) < 0) {
            return AVERROR_INVALIDDATA;
        }
        // read_timestamp is called inside ff_seek_frame_binary and leaves state dirty,
        // so reset_packet_state have to be called after it
        reset_packet_state(s);
    }

    return 0;
}

static GUIDParseTable *find_guid(ff_asf_guid guid)
{
    int j, ret;
    GUIDParseTable *g;

    g = gdef;
    for (j = 0; j < FF_ARRAY_ELEMS(gdef); j++) {
        if (!(ret = memcmp(guid, g->guid, sizeof(g->guid))))
            return g;
        g++;
    }

    return NULL;
}

static int detect_unknown_subobject(AVFormatContext *s, int64_t offset, int64_t size)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    GUIDParseTable *g = NULL;
    ff_asf_guid guid;
    int ret;

    while (avio_tell(pb) <= offset + size) {
        asf->offset = avio_tell(pb);
        if ((ret = ff_get_guid(pb, &guid)) < 0)
            return ret;
        swap_guid(guid);
        g = find_guid(guid);
        if (g) {
            if ((ret = g->read_object(s, g)) < 0)
                return ret;
        } else {
            g = av_mallocz(sizeof(GUIDParseTable));
            if (!g)
                return AVERROR(ENOMEM);
            g->name = "Unknown";
            g->is_subobject = 1;
            read_unknown(s, g);
            av_free(g);
        }
    }
    check_position(pb, offset, size);

    return 0;
}

static int asf_read_header(AVFormatContext *s)
{
    ASFContext *asf = s->priv_data;
    AVIOContext *pb = s->pb;
    GUIDParseTable *g = NULL;
    ff_asf_guid guid;
    int ret, is_seek = 0;

    asf->preroll    = 0;
    asf->seekable   = 1;
    asf->is_simple_index = 0;
    ff_get_guid(pb, &guid);
    if (ff_guidcmp(&guid, &ff_asf_header))
        return AVERROR_INVALIDDATA;
    asf->header_obj_size = avio_rl64(pb);
    avio_skip(pb, 6); // skip number of header objects and 2 reserved bytes
    asf->data_reached = 0;
    // 1  is here instead of pb->eof_reached because I skip Data for the first time,
    // read Indexes and get eof and then I seek back to the Data
    while (1) {
        asf->offset = avio_tell(pb);
        if (asf->offset > asf->header_obj_size && !asf->data_reached) {
            avio_seek(pb, asf->header_obj_size, SEEK_SET);
            asf->offset = asf->header_obj_size;
        }
        if ((ret = ff_get_guid(pb, &guid)) < 0) {
            if (ret == AVERROR_EOF && asf->data_reached) {
                avio_seek(pb, asf->data_offset, SEEK_SET);
                is_seek = 1;
                continue;
            } else
                return ret;
        }
        swap_guid(guid);
        g = find_guid(guid);
        if (g) {
            asf->unknown_offset = asf->offset;
            asf->is_header = 1;
            if ((ret = g->read_object(s, g)) < 0)
                return ret;
        }
        if (is_seek || !asf->seekable)
            break;
    }

    return 0;
}

AVInputFormat ff_asf_demuxer = {
    .name           = "asf",
    .long_name      = NULL_IF_CONFIG_SMALL("ASF (Advanced / Active Streaming Format)"),
    .priv_data_size = sizeof(ASFContext),
    .read_probe     = asf_probe,
    .read_header    = asf_read_header,
    .read_packet    = asf_read_packet,
    .read_close     = asf_read_close,
    .read_timestamp = asf_read_timestamp,
    .read_seek      = asf_read_seek,
    .flags          = AVFMT_NOBINSEARCH | AVFMT_NOGENSEARCH,
};
