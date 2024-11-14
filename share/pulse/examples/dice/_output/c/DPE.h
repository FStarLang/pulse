
#ifndef __DPE_H
#define __DPE_H

#include "krmllib.h"

#include "HACL.h"
#include "Pulse_Lib_SpinLock.h"
#include "EverCrypt_Base.h"

typedef struct EngineTypes_engine_record_t_s
{
  size_t l0_image_header_size;
  uint8_t *l0_image_header;
  uint8_t *l0_image_header_sig;
  size_t l0_binary_size;
  uint8_t *l0_binary;
  uint8_t *l0_binary_hash;
  uint8_t *l0_image_auth_pubkey;
}
EngineTypes_engine_record_t;

typedef struct L0Core_character_string_t_s
{
  uint32_t fst;
  FStar_Bytes_bytes snd;
}
L0Core_character_string_t;

typedef struct L0Core_octet_string_t_s
{
  uint32_t len;
  FStar_Bytes_bytes s;
}
L0Core_octet_string_t;

typedef struct L0Core_deviceIDCSR_ingredients_t_s
{
  int32_t ku;
  int32_t version;
  L0Core_character_string_t s_common;
  L0Core_character_string_t s_org;
  L0Core_character_string_t s_country;
}
L0Core_deviceIDCSR_ingredients_t;

typedef struct L0Core_aliasKeyCRT_ingredients_t_s
{
  int32_t version1;
  L0Core_octet_string_t serialNumber;
  L0Core_character_string_t i_common;
  L0Core_character_string_t i_org;
  L0Core_character_string_t i_country;
  FStar_Bytes_bytes notBefore;
  FStar_Bytes_bytes notAfter;
  L0Core_character_string_t s_common1;
  L0Core_character_string_t s_org1;
  L0Core_character_string_t s_country1;
  int32_t ku1;
  int32_t l0_version;
}
L0Core_aliasKeyCRT_ingredients_t;

typedef struct L0Types_l0_record_t_s
{
  uint8_t *fwid;
  uint32_t deviceID_label_len;
  uint8_t *deviceID_label;
  uint32_t aliasKey_label_len;
  uint8_t *aliasKey_label;
  L0Core_deviceIDCSR_ingredients_t deviceIDCSR_ingredients;
  L0Core_aliasKeyCRT_ingredients_t aliasKeyCRT_ingredients;
}
L0Types_l0_record_t;

typedef struct DPETypes_l1_context_t_s
{
  uint8_t *deviceID_pub;
  uint8_t *aliasKey_priv;
  uint8_t *aliasKey_pub;
  uint32_t deviceIDCSR_len;
  uint8_t *deviceIDCSR;
  uint32_t aliasKeyCRT_len;
  uint8_t *aliasKeyCRT;
}
DPETypes_l1_context_t;

#define DPETypes_Engine_context 0
#define DPETypes_L0_context 1
#define DPETypes_L1_context 2

typedef uint8_t DPETypes_context_t_tags;

typedef struct DPETypes_context_t_s
{
  DPETypes_context_t_tags tag;
  union {
    uint8_t *case_Engine_context;
    uint8_t *case_L0_context;
    DPETypes_l1_context_t case_L1_context;
  }
  ;
}
DPETypes_context_t;

#define DPETypes_Engine_record 0
#define DPETypes_L0_record 1

typedef uint8_t DPETypes_record_t_tags;

typedef struct DPETypes_record_t_s
{
  DPETypes_record_t_tags tag;
  union {
    EngineTypes_engine_record_t case_Engine_record;
    L0Types_l0_record_t case_L0_record;
  }
  ;
}
DPETypes_record_t;

typedef uint16_t DPE_sid_t;

typedef DPETypes_context_t DPE_session_state__Available__payload;

#define DPE_SessionStart 0
#define DPE_Available 1
#define DPE_InUse 2
#define DPE_SessionClosed 3
#define DPE_SessionError 4

typedef uint8_t DPE_session_state_tags;

typedef struct DPE_session_state_s
{
  DPE_session_state_tags tag;
  DPE_session_state__Available__payload _0;
}
DPE_session_state;

bool DPE_uu___is_SessionStart(DPE_session_state projectee);

bool DPE_uu___is_Available(DPE_session_state projectee);

bool DPE_uu___is_InUse(DPE_session_state projectee);

bool DPE_uu___is_SessionClosed(DPE_session_state projectee);

bool DPE_uu___is_SessionError(DPE_session_state projectee);

#define Pulse_Lib_HashTable_Spec_Clean 0
#define Pulse_Lib_HashTable_Spec_Zombie 1
#define Pulse_Lib_HashTable_Spec_Used 2

typedef uint8_t Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state_tags;

typedef struct Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state_s
{
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state_tags tag;
  uint16_t k;
  DPE_session_state v;
}
Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state;

typedef struct DPE_ht_t_s
{
  size_t sz;
  size_t (*hashf)(uint16_t x0);
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *contents;
}
DPE_ht_t;

typedef struct DPE_st_s
{
  uint16_t st_ctr;
  DPE_ht_t st_tbl;
}
DPE_st;

#define FStar_Pervasives_Native_None 0
#define FStar_Pervasives_Native_Some 1

typedef uint8_t FStar_Pervasives_Native_option__DPE_st_tags;

typedef struct FStar_Pervasives_Native_option__uint16_t_s
{
  FStar_Pervasives_Native_option__DPE_st_tags tag;
  uint16_t v;
}
FStar_Pervasives_Native_option__uint16_t;

FStar_Pervasives_Native_option__uint16_t DPE_open_session(void);

void DPE_initialize_context(uint16_t sid, uint8_t *uds);

bool DPE_derive_child(uint16_t sid, DPETypes_record_t record);

void DPE_close_session(uint16_t sid);

uint32_t DPE_certify_key(uint16_t sid, uint8_t *pub_key, uint32_t crt_len, uint8_t *crt);

void DPE_sign(uint16_t sid, uint8_t *signature, size_t msg_len, uint8_t *msg);


#define __DPE_H_DEFINED
#endif
