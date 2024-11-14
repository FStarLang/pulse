
#include "internal/DPE.h"

static void fill__uint8_t(size_t l, uint8_t *a, uint8_t v)
{
  size_t i = (size_t)0U;
  size_t vi0 = i;
  bool cond = vi0 < l;
  while (cond)
  {
    size_t vi = i;
    a[vi] = v;
    i = vi + (size_t)1U;
    size_t vi0 = i;
    cond = vi0 < l;
  }
}

static void zeroize(size_t l, uint8_t *a)
{
  fill__uint8_t(l, a, 0U);
}

static size_t size_t_mod(size_t x, size_t y)
{
  return x % y;
}

static size_t uds_len = (size_t)32U;

#define DICE_SUCCESS 0
#define DICE_ERROR 1

typedef uint8_t dice_return_code;

static uint8_t *vec_to_array__uint8_t(uint8_t *v)
{
  return v;
}

static bool compare__uint8_t(size_t l, uint8_t *a1, uint8_t *a2)
{
  size_t i = (size_t)0U;
  size_t vi0 = i;
  bool cond;
  if (vi0 < l)
  {
    uint8_t v1 = a1[vi0];
    uint8_t v2 = a2[vi0];
    cond = v1 == v2;
  }
  else
    cond = false;
  while (cond)
  {
    size_t vi = i;
    i = vi + (size_t)1U;
    size_t vi0 = i;
    bool ite;
    if (vi0 < l)
    {
      uint8_t v1 = a1[vi0];
      uint8_t v2 = a2[vi0];
      ite = v1 == v2;
    }
    else
      ite = false;
    cond = ite;
  }
  size_t vi = i;
  return vi == l;
}

typedef struct __EngineTypes_engine_record_t_bool_s
{
  EngineTypes_engine_record_t fst;
  bool snd;
}
__EngineTypes_engine_record_t_bool;

static __EngineTypes_engine_record_t_bool
authenticate_l0_image(EngineTypes_engine_record_t record)
{
  bool
  valid_header_sig =
    HACL_ed25519_verify(vec_to_array__uint8_t(record.l0_image_auth_pubkey),
      vec_to_array__uint8_t(record.l0_image_header),
      record.l0_image_header_size,
      vec_to_array__uint8_t(record.l0_image_header_sig));
  bool b = false;
  KRML_HOST_IGNORE(&b);
  if (valid_header_sig)
  {
    uint8_t *hash_buf = KRML_HOST_CALLOC((size_t)32U, sizeof (uint8_t));
    HACL_hacl_hash(HACL_dice_hash_alg0(),
      record.l0_binary_size,
      vec_to_array__uint8_t(record.l0_binary),
      hash_buf);
    bool
    res = compare__uint8_t((size_t)32U, hash_buf, vec_to_array__uint8_t(record.l0_binary_hash));
    return ((__EngineTypes_engine_record_t_bool){ .fst = record, .snd = res });
  }
  else
    return ((__EngineTypes_engine_record_t_bool){ .fst = record, .snd = false });
}

static EngineTypes_engine_record_t
compute_cdi(uint8_t *cdi, uint8_t *uds, EngineTypes_engine_record_t record)
{
  uint8_t *uds_digest = KRML_HOST_CALLOC((size_t)32U, sizeof (uint8_t));
  uint8_t *l0_digest = KRML_HOST_CALLOC((size_t)32U, sizeof (uint8_t));
  HACL_hacl_hash(HACL_dice_hash_alg0(), uds_len, uds, uds_digest);
  HACL_hacl_hash(HACL_dice_hash_alg0(),
    record.l0_binary_size,
    vec_to_array__uint8_t(record.l0_binary),
    l0_digest);
  HACL_hacl_hmac(HACL_dice_hash_alg0(), cdi, uds_digest, (size_t)32U, l0_digest, (size_t)32U);
  return record;
}

static bool snd__EngineTypes_engine_record_t_bool(__EngineTypes_engine_record_t_bool x)
{
  return x.snd;
}

static EngineTypes_engine_record_t
fst__EngineTypes_engine_record_t_bool(__EngineTypes_engine_record_t_bool x)
{
  return x.fst;
}

typedef struct __EngineTypes_engine_record_t_EngineTypes_dice_return_code_s
{
  EngineTypes_engine_record_t fst;
  dice_return_code snd;
}
__EngineTypes_engine_record_t_EngineTypes_dice_return_code;

static __EngineTypes_engine_record_t_EngineTypes_dice_return_code
engine_main(uint8_t *cdi, uint8_t *uds, EngineTypes_engine_record_t record)
{
  __EngineTypes_engine_record_t_bool b = authenticate_l0_image(record);
  if (snd__EngineTypes_engine_record_t_bool(b))
  {
    EngineTypes_engine_record_t
    record1 = compute_cdi(cdi, uds, fst__EngineTypes_engine_record_t_bool(b));
    return
      (
        (__EngineTypes_engine_record_t_EngineTypes_dice_return_code){
          .fst = record1,
          .snd = DICE_SUCCESS
        }
      );
  }
  else
  {
    __EngineTypes_engine_record_t_EngineTypes_dice_return_code
    res = { .fst = fst__EngineTypes_engine_record_t_bool(b), .snd = DICE_ERROR };
    return res;
  }
}

extern Pulse_Lib_SpinLock_lock Pulse_Lib_SpinLock_new_lock(void);

extern void Pulse_Lib_SpinLock_acquire(Pulse_Lib_SpinLock_lock l);

extern void Pulse_Lib_SpinLock_release(Pulse_Lib_SpinLock_lock l);

extern uint32_t
L0Core_len_of_deviceIDCRI(
  int32_t version,
  L0Core_character_string_t s_common,
  L0Core_character_string_t s_org,
  L0Core_character_string_t s_country
);

extern uint32_t L0Core_len_of_deviceIDCSR(uint32_t cri_len);

extern uint32_t
L0Core_len_of_aliasKeyTBS(
  L0Core_octet_string_t serialNumber,
  L0Core_character_string_t i_common,
  L0Core_character_string_t i_org,
  L0Core_character_string_t i_country,
  L0Core_character_string_t s_common,
  L0Core_character_string_t s_org,
  L0Core_character_string_t s_country,
  int32_t l0_version
);

extern uint32_t L0Core_len_of_aliasKeyCRT(uint32_t tbs_len);

extern void
L0Core_l0(
  uint8_t *cdi,
  uint8_t *fwid,
  uint32_t deviceID_label_len,
  uint8_t *deviceID_label,
  uint32_t aliasKey_label_len,
  uint8_t *aliasKey_label,
  L0Core_deviceIDCSR_ingredients_t deviceIDCSR_ingredients,
  L0Core_aliasKeyCRT_ingredients_t aliasKeyCRT_ingredients,
  uint8_t *deviceID_pub,
  uint8_t *aliasKey_pub,
  uint8_t *aliasKey_priv,
  uint32_t deviceIDCSR_len,
  uint8_t *deviceIDCSR_buf,
  uint32_t aliasKeyCRT_len,
  uint8_t *aliasKeyCRT_buf
);

static uint32_t len_of_deviceIDCSR(L0Core_deviceIDCSR_ingredients_t x)
{
  return
    L0Core_len_of_deviceIDCSR(L0Core_len_of_deviceIDCRI(x.version,
        x.s_common,
        x.s_org,
        x.s_country));
}

static uint32_t len_of_aliasKeyCRT(L0Core_aliasKeyCRT_ingredients_t x)
{
  return
    L0Core_len_of_aliasKeyCRT(L0Core_len_of_aliasKeyTBS(x.serialNumber,
        x.i_common,
        x.i_org,
        x.i_country,
        x.s_common1,
        x.s_org1,
        x.s_country1,
        x.l0_version));
}

typedef uint8_t *engine_context_t;

static uint8_t *mk_engine_context_t(uint8_t *uds)
{
  return uds;
}

typedef uint8_t *l0_context_t;

static uint8_t *mk_l0_context_t(uint8_t *cdi)
{
  return cdi;
}

static DPETypes_l1_context_t
mk_l1_context_t(
  uint8_t *deviceID_pub,
  uint8_t *aliasKey_pub,
  uint8_t *aliasKey_priv,
  uint32_t deviceIDCSR_len,
  uint8_t *deviceIDCSR,
  uint32_t aliasKeyCRT_len,
  uint8_t *aliasKeyCRT
)
{
  return
    (
      (DPETypes_l1_context_t){
        .deviceID_pub = deviceID_pub,
        .aliasKey_priv = aliasKey_priv,
        .aliasKey_pub = aliasKey_pub,
        .deviceIDCSR_len = deviceIDCSR_len,
        .deviceIDCSR = deviceIDCSR,
        .aliasKeyCRT_len = aliasKeyCRT_len,
        .aliasKeyCRT = aliasKeyCRT
      }
    );
}

static DPETypes_context_t mk_context_t_engine(uint8_t *c)
{
  return ((DPETypes_context_t){ .tag = DPETypes_Engine_context, { .case_Engine_context = c } });
}

bool DPE_uu___is_SessionStart(DPE_session_state projectee)
{
  if (projectee.tag == DPE_SessionStart)
    return true;
  else
    return false;
}

bool DPE_uu___is_Available(DPE_session_state projectee)
{
  if (projectee.tag == DPE_Available)
    return true;
  else
    return false;
}

bool DPE_uu___is_InUse(DPE_session_state projectee)
{
  if (projectee.tag == DPE_InUse)
    return true;
  else
    return false;
}

bool DPE_uu___is_SessionClosed(DPE_session_state projectee)
{
  if (projectee.tag == DPE_SessionClosed)
    return true;
  else
    return false;
}

bool DPE_uu___is_SessionError(DPE_session_state projectee)
{
  if (projectee.tag == DPE_SessionError)
    return true;
  else
    return false;
}

static size_t sid_hash(uint16_t s)
{
  return (size_t)s;
}

static Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st
new_mutex__FStar_Pervasives_Native_option_DPE_st(FStar_Pervasives_Native_option__DPE_st x)
{
  FStar_Pervasives_Native_option__DPE_st
  *r = KRML_HOST_MALLOC(sizeof (FStar_Pervasives_Native_option__DPE_st));
  r[0U] = x;
  Pulse_Lib_SpinLock_lock l = Pulse_Lib_SpinLock_new_lock();
  return ((Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st){ .r = r, .l = l });
}

Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st DPE_initialize_global_state(void)
{
  Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st
  m =
    new_mutex__FStar_Pervasives_Native_option_DPE_st((
        (FStar_Pervasives_Native_option__DPE_st){ .tag = FStar_Pervasives_Native_None }
      ));
  return m;
}

Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st DPE_gst;

static FStar_Pervasives_Native_option__uint16_t safe_incr(uint16_t i)
{
  if (i < 0xffffU)
    return
      (
        (FStar_Pervasives_Native_option__uint16_t){
          .tag = FStar_Pervasives_Native_Some,
          .v = (uint32_t)i + 1U
        }
      );
  else
    return ((FStar_Pervasives_Native_option__uint16_t){ .tag = FStar_Pervasives_Native_None });
}

static Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
op_Array_Access__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *v,
  size_t i
)
{
  return v[i];
}

static void
op_Array_Assignment__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *v,
  size_t i,
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state x
)
{
  v[i] = x;
}

static Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state **r,
  size_t i,
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state x
)
{
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *vc = *r;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
  y = op_Array_Access__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(vc, i);
  op_Array_Assignment__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(vc, i, x);
  return y;
}

typedef struct __bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state_s
{
  bool fst;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state snd;
}
__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state;

static __bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state
is_used__uint16_t_DPE_session_state(
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state c
)
{
  if (c.tag == Pulse_Lib_HashTable_Spec_Used)
    return
      ((__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state){ .fst = true, .snd = c });
  else
    return
      ((__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state){ .fst = false, .snd = c });
}

static Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
snd__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(
  __bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state x
)
{
  return x.snd;
}

static bool
fst__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(
  __bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state x
)
{
  return x.fst;
}

static DPE_ht_t
mk_ht__uint16_t_DPE_session_state(
  size_t sz,
  size_t (*hashf)(uint16_t x0),
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *contents
)
{
  return ((DPE_ht_t){ .sz = sz, .hashf = hashf, .contents = contents });
}

typedef struct __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool_s
{
  DPE_ht_t fst;
  bool snd;
}
__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool;

static __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool
not_full__uint16_t_DPE_session_state(DPE_ht_t ht)
{
  size_t (*hashf)(uint16_t x0) = ht.hashf;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *contents = ht.contents;
  size_t i = (size_t)0U;
  size_t vi0 = i;
  bool cond;
  if (vi0 < ht.sz)
  {
    Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
    c =
      replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
        vi0,
        (
          (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
            .tag = Pulse_Lib_HashTable_Spec_Zombie
          }
        ));
    __bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state
    b = is_used__uint16_t_DPE_session_state(c);
    replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
      vi0,
      snd__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(b));
    cond = fst__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(b);
  }
  else
    cond = false;
  while (cond)
  {
    size_t vi = i;
    i = vi + (size_t)1U;
    size_t vi0 = i;
    bool ite;
    if (vi0 < ht.sz)
    {
      Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
      c =
        replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
          vi0,
          (
            (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
              .tag = Pulse_Lib_HashTable_Spec_Zombie
            }
          ));
      __bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state
      b = is_used__uint16_t_DPE_session_state(c);
      replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
        vi0,
        snd__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(b));
      ite = fst__bool_Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(b);
    }
    else
      ite = false;
    cond = ite;
  }
  size_t vi = i;
  bool res = vi < ht.sz;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *vcontents = contents;
  DPE_ht_t ht1 = mk_ht__uint16_t_DPE_session_state(ht.sz, hashf, vcontents);
  return
    ((__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool){ .fst = ht1, .snd = res });
}

static bool
snd__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool(
  __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool x
)
{
  return x.snd;
}

static void
write_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state **r,
  size_t i,
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state x
)
{
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *vc = *r;
  op_Array_Assignment__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(vc, i, x);
}

typedef struct option__size_t_s
{
  FStar_Pervasives_Native_option__DPE_st_tags tag;
  size_t v;
}
option__size_t;

typedef struct
__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t_s
{
  DPE_ht_t fst;
  option__size_t snd;
}
__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t;

static __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t
lookup__uint16_t_DPE_session_state(DPE_ht_t ht, uint16_t k)
{
  size_t (*hashf)(uint16_t x0) = ht.hashf;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *contents = ht.contents;
  size_t cidx = size_t_mod(hashf(k), ht.sz);
  size_t off = (size_t)0U;
  bool cont = true;
  option__size_t ret = { .tag = FStar_Pervasives_Native_None };
  size_t voff0 = off;
  bool vcont0 = cont;
  bool cond = voff0 <= ht.sz && vcont0 == true;
  while (cond)
  {
    size_t voff = off;
    if (voff == ht.sz)
      cont = false;
    else
    {
      size_t sum = cidx + voff;
      size_t idx = size_t_mod(sum, ht.sz);
      Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
      c =
        replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
          idx,
          (
            (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
              .tag = Pulse_Lib_HashTable_Spec_Zombie
            }
          ));
      if (c.tag == Pulse_Lib_HashTable_Spec_Used)
      {
        DPE_session_state v_ = c.v;
        uint16_t k_ = c.k;
        if (k_ == k)
        {
          cont = false;
          ret = ((option__size_t){ .tag = FStar_Pervasives_Native_Some, .v = idx });
          replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
            idx,
            (
              (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
                .tag = Pulse_Lib_HashTable_Spec_Used,
                .k = k_,
                .v = v_
              }
            ));
        }
        else
        {
          off = voff + (size_t)1U;
          replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
            idx,
            (
              (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
                .tag = Pulse_Lib_HashTable_Spec_Used,
                .k = k_,
                .v = v_
              }
            ));
        }
      }
      else if (c.tag == Pulse_Lib_HashTable_Spec_Clean)
      {
        cont = false;
        replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents, idx, c);
      }
      else if (c.tag == Pulse_Lib_HashTable_Spec_Zombie)
      {
        off = voff + (size_t)1U;
        replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents, idx, c);
      }
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    size_t voff0 = off;
    bool vcont = cont;
    cond = voff0 <= ht.sz && vcont == true;
  }
  option__size_t o = ret;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *vcontents = contents;
  DPE_ht_t ht1 = mk_ht__uint16_t_DPE_session_state(ht.sz, ht.hashf, vcontents);
  return
    (
      (__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t){
        .fst = ht1,
        .snd = o
      }
    );
}

static DPE_ht_t
fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t(
  __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t
  x
)
{
  return x.fst;
}

static option__size_t
snd__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t(
  __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t
  x
)
{
  return x.snd;
}

static Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
mk_used_cell__uint16_t_DPE_session_state(uint16_t k, DPE_session_state v)
{
  return
    (
      (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
        .tag = Pulse_Lib_HashTable_Spec_Used,
        .k = k,
        .v = v
      }
    );
}

static __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool
insert__uint16_t_DPE_session_state(DPE_ht_t ht, uint16_t k, DPE_session_state v)
{
  size_t (*hashf)(uint16_t x0) = ht.hashf;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *contents = ht.contents;
  size_t cidx = size_t_mod(hashf(k), ht.sz);
  size_t off = (size_t)0U;
  bool cont = true;
  size_t idx = (size_t)0U;
  bool vcont = cont;
  bool cond = vcont == true;
  while (cond)
  {
    size_t voff = off;
    if (voff == ht.sz)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      size_t sum = cidx + voff;
      size_t vidx = size_t_mod(sum, ht.sz);
      Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
      c =
        replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
          vidx,
          (
            (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
              .tag = Pulse_Lib_HashTable_Spec_Zombie
            }
          ));
      if (c.tag == Pulse_Lib_HashTable_Spec_Used)
      {
        DPE_session_state v_ = c.v;
        uint16_t k_ = c.k;
        if (k_ == k)
        {
          write_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
            vidx,
            (
              (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
                .tag = Pulse_Lib_HashTable_Spec_Used,
                .k = k_,
                .v = v_
              }
            ));
          cont = false;
          idx = vidx;
        }
        else
        {
          write_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
            vidx,
            (
              (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
                .tag = Pulse_Lib_HashTable_Spec_Used,
                .k = k_,
                .v = v_
              }
            ));
          off = voff + (size_t)1U;
        }
      }
      else if (c.tag == Pulse_Lib_HashTable_Spec_Clean)
      {
        write_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
          vidx,
          (
            (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
              .tag = Pulse_Lib_HashTable_Spec_Clean
            }
          ));
        cont = false;
        idx = vidx;
      }
      else if (c.tag == Pulse_Lib_HashTable_Spec_Zombie)
      {
        Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *vcontents = contents;
        DPE_ht_t ht1 = { .sz = ht.sz, .hashf = hashf, .contents = vcontents };
        __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t
        res = lookup__uint16_t_DPE_session_state(ht1, k);
        contents =
          fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t(res).contents;
        option__size_t
        o =
          snd__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t(res);
        if (o.tag == FStar_Pervasives_Native_Some)
        {
          size_t p = o.v;
          write_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
            p,
            (
              (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
                .tag = Pulse_Lib_HashTable_Spec_Zombie
              }
            ));
          cont = false;
          idx = vidx;
        }
        else if (o.tag == FStar_Pervasives_Native_None)
        {
          cont = false;
          idx = vidx;
        }
        else
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
      }
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    bool vcont = cont;
    cond = vcont == true;
  }
  bool vcont0 = cont;
  size_t vidx = idx;
  if (vcont0 == false)
  {
    write_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
      vidx,
      mk_used_cell__uint16_t_DPE_session_state(k, v));
    Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *vcontents = contents;
    DPE_ht_t ht1 = mk_ht__uint16_t_DPE_session_state(ht.sz, hashf, vcontents);
    return
      ((__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool){ .fst = ht1, .snd = true });
  }
  else
  {
    Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *vcontents = contents;
    DPE_ht_t ht1 = mk_ht__uint16_t_DPE_session_state(ht.sz, hashf, vcontents);
    return
      (
        (__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool){
          .fst = ht1,
          .snd = false
        }
      );
  }
}

static DPE_ht_t
fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool(
  __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool x
)
{
  return x.fst;
}

static __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool
insert_if_not_full__uint16_t_DPE_session_state(DPE_ht_t ht, uint16_t k, DPE_session_state v)
{
  __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool
  b = not_full__uint16_t_DPE_session_state(ht);
  if (snd__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool(b))
    return
      insert__uint16_t_DPE_session_state(fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool(b),
        k,
        v);
  else
  {
    __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool
    res =
      { .fst = fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool(b), .snd = false };
    return res;
  }
}

typedef struct __DPE_st_FStar_Pervasives_Native_option_uint16_t_s
{
  DPE_st fst;
  FStar_Pervasives_Native_option__uint16_t snd;
}
__DPE_st_FStar_Pervasives_Native_option_uint16_t;

static __DPE_st_FStar_Pervasives_Native_option_uint16_t __open_session(DPE_st s)
{
  uint16_t ctr = s.st_ctr;
  DPE_ht_t tbl = s.st_tbl;
  FStar_Pervasives_Native_option__uint16_t copt = safe_incr(ctr);
  if (copt.tag == FStar_Pervasives_Native_None)
  {
    DPE_st s1 = { .st_ctr = ctr, .st_tbl = tbl };
    return
      (
        (__DPE_st_FStar_Pervasives_Native_option_uint16_t){
          .fst = s1,
          .snd = { .tag = FStar_Pervasives_Native_None }
        }
      );
  }
  else if (copt.tag == FStar_Pervasives_Native_Some)
  {
    uint16_t ctr1 = copt.v;
    __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool
    ret =
      insert_if_not_full__uint16_t_DPE_session_state(tbl,
        ctr,
        ((DPE_session_state){ .tag = DPE_SessionStart }));
    DPE_ht_t tbl1 = fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool(ret);
    bool b = snd__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_bool(ret);
    if (b)
    {
      DPE_st s1 = { .st_ctr = ctr1, .st_tbl = tbl1 };
      return
        (
          (__DPE_st_FStar_Pervasives_Native_option_uint16_t){
            .fst = s1,
            .snd = { .tag = FStar_Pervasives_Native_Some, .v = ctr }
          }
        );
    }
    else
    {
      DPE_st s1 = { .st_ctr = ctr, .st_tbl = tbl1 };
      return
        (
          (__DPE_st_FStar_Pervasives_Native_option_uint16_t){
            .fst = s1,
            .snd = { .tag = FStar_Pervasives_Native_None }
          }
        );
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
*alloc__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state x,
  size_t n
)
{
  KRML_CHECK_SIZE(sizeof (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state), n);
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
  *buf = KRML_HOST_MALLOC(sizeof (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state) * n);
  for (uint32_t _i = 0U; _i < n; ++_i)
    buf[_i] = x;
  return buf;
}

static DPE_ht_t alloc__uint16_t_DPE_session_state(size_t (*hashf)(uint16_t x0), size_t l)
{
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
  *contents =
    alloc__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state((
        (Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state){
          .tag = Pulse_Lib_HashTable_Spec_Clean
        }
      ),
      l);
  DPE_ht_t ht = mk_ht__uint16_t_DPE_session_state(l, hashf, contents);
  return ht;
}

static DPE_st maybe_mk_session_tbl(FStar_Pervasives_Native_option__DPE_st sopt)
{
  if (sopt.tag == FStar_Pervasives_Native_None)
  {
    DPE_ht_t tbl = alloc__uint16_t_DPE_session_state(sid_hash, (size_t)256U);
    return ((DPE_st){ .st_ctr = 0U, .st_tbl = tbl });
  }
  else if (sopt.tag == FStar_Pervasives_Native_Some)
    return sopt.v;
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static FStar_Pervasives_Native_option__DPE_st
*lock__FStar_Pervasives_Native_option_DPE_st(
  Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st m
)
{
  Pulse_Lib_SpinLock_acquire(m.l);
  return m.r;
}

static Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st
snd_____Pulse_Lib_Mutex_mutex_FStar_Pervasives_Native_option_DPE_st(
  Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st x
)
{
  return x;
}

static FStar_Pervasives_Native_option__DPE_st
replace__FStar_Pervasives_Native_option_DPE_st(
  FStar_Pervasives_Native_option__DPE_st *r,
  FStar_Pervasives_Native_option__DPE_st x
)
{
  FStar_Pervasives_Native_option__DPE_st y = *r;
  *r = x;
  return y;
}

static FStar_Pervasives_Native_option__DPE_st
replace__FStar_Pervasives_Native_option_DPE_st0(
  FStar_Pervasives_Native_option__DPE_st *r,
  FStar_Pervasives_Native_option__DPE_st y
)
{
  return replace__FStar_Pervasives_Native_option_DPE_st(r, y);
}

static DPE_st
fst__DPE_st_FStar_Pervasives_Native_option_uint16_t(
  __DPE_st_FStar_Pervasives_Native_option_uint16_t x
)
{
  return x.fst;
}

static FStar_Pervasives_Native_option__uint16_t
snd__DPE_st_FStar_Pervasives_Native_option_uint16_t(
  __DPE_st_FStar_Pervasives_Native_option_uint16_t x
)
{
  return x.snd;
}

static void
op_Colon_Equals__FStar_Pervasives_Native_option_DPE_st(
  FStar_Pervasives_Native_option__DPE_st *r,
  FStar_Pervasives_Native_option__DPE_st y
)
{
  *r = y;
}

static void
unlock__FStar_Pervasives_Native_option_DPE_st(
  Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st m
)
{
  Pulse_Lib_SpinLock_release(m.l);
}

FStar_Pervasives_Native_option__uint16_t DPE_open_session(void)
{
  Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st r = DPE_gst;
  FStar_Pervasives_Native_option__DPE_st
  *mg =
    lock__FStar_Pervasives_Native_option_DPE_st(snd_____Pulse_Lib_Mutex_mutex_FStar_Pervasives_Native_option_DPE_st(r));
  FStar_Pervasives_Native_option__DPE_st
  sopt =
    replace__FStar_Pervasives_Native_option_DPE_st0(mg,
      ((FStar_Pervasives_Native_option__DPE_st){ .tag = FStar_Pervasives_Native_None }));
  DPE_st s = maybe_mk_session_tbl(sopt);
  __DPE_st_FStar_Pervasives_Native_option_uint16_t ret = __open_session(s);
  DPE_st s1 = fst__DPE_st_FStar_Pervasives_Native_option_uint16_t(ret);
  FStar_Pervasives_Native_option__uint16_t
  sid_opt = snd__DPE_st_FStar_Pervasives_Native_option_uint16_t(ret);
  op_Colon_Equals__FStar_Pervasives_Native_option_DPE_st(mg,
    ((FStar_Pervasives_Native_option__DPE_st){ .tag = FStar_Pervasives_Native_Some, .v = s1 }));
  unlock__FStar_Pervasives_Native_option_DPE_st(snd_____Pulse_Lib_Mutex_mutex_FStar_Pervasives_Native_option_DPE_st(r));
  return sid_opt;
}

typedef struct __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state_s
{
  DPE_ht_t fst;
  DPE_session_state snd;
}
__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state;

static __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state
replace__uint16_t_DPE_session_state(DPE_ht_t ht, size_t idx, uint16_t k, DPE_session_state v)
{
  size_t (*hashf)(uint16_t x0) = ht.hashf;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *contents = ht.contents;
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state
  v_ =
    replace_i_ref__Pulse_Lib_HashTable_Spec_cell_uint16_t_DPE_session_state(&contents,
      idx,
      mk_used_cell__uint16_t_DPE_session_state(k, v));
  Pulse_Lib_HashTable_Spec_cell__uint16_t_DPE_session_state *vcontents = contents;
  DPE_ht_t ht1 = mk_ht__uint16_t_DPE_session_state(ht.sz, hashf, vcontents);
  if (v_.tag == Pulse_Lib_HashTable_Spec_Used)
  {
    DPE_session_state v_1 = v_.v;
    return
      (
        (__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state){
          .fst = ht1,
          .snd = v_1
        }
      );
  }
  else if (v_.tag == Pulse_Lib_HashTable_Spec_Clean)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (v_.tag == Pulse_Lib_HashTable_Spec_Zombie)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static DPE_ht_t
fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state(
  __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state x
)
{
  return x.fst;
}

static DPE_session_state
snd__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state(
  __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state x
)
{
  return x.snd;
}

static DPE_session_state replace_session(uint16_t sid, DPE_session_state sst)
{
  Pulse_Lib_Mutex_mutex__FStar_Pervasives_Native_option_DPE_st r = DPE_gst;
  FStar_Pervasives_Native_option__DPE_st
  *mg =
    lock__FStar_Pervasives_Native_option_DPE_st(snd_____Pulse_Lib_Mutex_mutex_FStar_Pervasives_Native_option_DPE_st(r));
  FStar_Pervasives_Native_option__DPE_st
  sopt =
    replace__FStar_Pervasives_Native_option_DPE_st0(mg,
      ((FStar_Pervasives_Native_option__DPE_st){ .tag = FStar_Pervasives_Native_None }));
  if (sopt.tag == FStar_Pervasives_Native_None)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (sopt.tag == FStar_Pervasives_Native_Some)
  {
    DPE_st s = sopt.v;
    uint16_t ctr = s.st_ctr;
    DPE_ht_t tbl = s.st_tbl;
    if (sid < ctr)
    {
      __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t
      ret = lookup__uint16_t_DPE_session_state(tbl, sid);
      DPE_ht_t
      tbl1 =
        fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t(ret);
      option__size_t
      idx =
        snd__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_FStar_Pervasives_Native_option_size_t(ret);
      if (idx.tag == FStar_Pervasives_Native_Some)
      {
        size_t idx1 = idx.v;
        __Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state
        ret1 = replace__uint16_t_DPE_session_state(tbl1, idx1, sid, sst);
        DPE_ht_t
        tbl2 = fst__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state(ret1);
        DPE_session_state
        st1 = snd__Pulse_Lib_HashTable_Type_ht_t_uint16_t_DPE_session_state_DPE_session_state(ret1);
        DPE_st s1 = { .st_ctr = ctr, .st_tbl = tbl2 };
        op_Colon_Equals__FStar_Pervasives_Native_option_DPE_st(mg,
          ((FStar_Pervasives_Native_option__DPE_st){ .tag = FStar_Pervasives_Native_Some, .v = s1 }));
        unlock__FStar_Pervasives_Native_option_DPE_st(snd_____Pulse_Lib_Mutex_mutex_FStar_Pervasives_Native_option_DPE_st(r));
        return st1;
      }
      else if (idx.tag == FStar_Pervasives_Native_None)
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "Pulse.Lib.Dv.unreachable");
        KRML_HOST_EXIT(255U);
      }
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static uint8_t *alloc__uint8_t(uint8_t x, size_t n)
{
  KRML_CHECK_SIZE(sizeof (uint8_t), n);
  uint8_t *buf = KRML_HOST_MALLOC(sizeof (uint8_t) * n);
  for (uint32_t _i = 0U; _i < n; ++_i)
    buf[_i] = x;
  return buf;
}

static void memcpy_l__uint8_t(size_t l, uint8_t *src, uint8_t *dst)
{
  size_t i = (size_t)0U;
  size_t vi0 = i;
  bool cond = vi0 < l;
  while (cond)
  {
    size_t vi = i;
    uint8_t x = src[vi];
    dst[vi] = x;
    i = vi + (size_t)1U;
    size_t vi0 = i;
    cond = vi0 < l;
  }
}

static void memcpy__uint8_t(size_t l, uint8_t *src, uint8_t *dst)
{
  memcpy_l__uint8_t(l, src, dst);
}

static DPETypes_context_t init_engine_ctxt(uint8_t *uds)
{
  uint8_t *uds_buf = alloc__uint8_t(0U, uds_len);
  memcpy__uint8_t(uds_len, uds, vec_to_array__uint8_t(uds_buf));
  uint8_t *engine_context = mk_engine_context_t(uds_buf);
  DPETypes_context_t ctxt = mk_context_t_engine(engine_context);
  return ctxt;
}

void DPE_initialize_context(uint16_t sid, uint8_t *uds)
{
  DPE_session_state s = replace_session(sid, ((DPE_session_state){ .tag = DPE_InUse }));
  if (s.tag == DPE_SessionStart)
  {
    DPETypes_context_t context = init_engine_ctxt(uds);
    DPE_session_state s1 = { .tag = DPE_Available, ._0 = context };
    DPE_session_state s2 = replace_session(sid, s1);
    KRML_MAYBE_UNUSED_VAR(s2);
  }
  else if (s.tag == DPE_InUse)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_SessionClosed)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_SessionError)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_Available)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static uint8_t *init_l0_ctxt(uint8_t *cdi)
{
  uint8_t *cdi_buf = alloc__uint8_t(0U, (size_t)32U);
  memcpy__uint8_t((size_t)32U, cdi, vec_to_array__uint8_t(cdi_buf));
  uint8_t *l0_context = mk_l0_context_t(cdi_buf);
  return l0_context;
}

static DPETypes_l1_context_t
init_l1_ctxt(
  uint8_t *deviceID_pub,
  uint8_t *aliasKey_priv,
  uint8_t *aliasKey_pub,
  uint32_t deviceIDCSR_len,
  uint8_t *deviceIDCSR,
  uint32_t aliasKeyCRT_len,
  uint8_t *aliasKeyCRT
)
{
  DPETypes_l1_context_t
  ctxt =
    mk_l1_context_t(deviceID_pub,
      aliasKey_pub,
      aliasKey_priv,
      deviceIDCSR_len,
      deviceIDCSR,
      aliasKeyCRT_len,
      aliasKeyCRT);
  return ctxt;
}

static void free__uint8_t(uint8_t *v)
{
  KRML_HOST_FREE(v);
}

static void destroy_ctxt(DPETypes_context_t ctxt)
{
  if (ctxt.tag == DPETypes_Engine_context)
  {
    uint8_t *c = ctxt.case_Engine_context;
    free__uint8_t(c);
  }
  else if (ctxt.tag == DPETypes_L0_context)
  {
    uint8_t *c = ctxt.case_L0_context;
    free__uint8_t(c);
  }
  else if (ctxt.tag == DPETypes_L1_context)
  {
    DPETypes_l1_context_t c = ctxt.case_L1_context;
    free__uint8_t(c.deviceID_pub);
    free__uint8_t(c.aliasKey_priv);
    free__uint8_t(c.aliasKey_pub);
    free__uint8_t(c.aliasKeyCRT);
    free__uint8_t(c.deviceIDCSR);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static EngineTypes_engine_record_t
fst__EngineTypes_engine_record_t_EngineTypes_dice_return_code(
  __EngineTypes_engine_record_t_EngineTypes_dice_return_code x
)
{
  return x.fst;
}

static dice_return_code
snd__EngineTypes_engine_record_t_EngineTypes_dice_return_code(
  __EngineTypes_engine_record_t_EngineTypes_dice_return_code x
)
{
  return x.snd;
}

typedef struct option__DPETypes_context_t_s
{
  FStar_Pervasives_Native_option__DPE_st_tags tag;
  DPETypes_context_t v;
}
option__DPETypes_context_t;

static option__DPETypes_context_t
derive_child_from_context(DPETypes_context_t context, DPETypes_record_t record)
{
  if (context.tag == DPETypes_Engine_context)
  {
    uint8_t *c = context.case_Engine_context;
    if (record.tag == DPETypes_Engine_record)
    {
      EngineTypes_engine_record_t r = record.case_Engine_record;
      uint8_t *cdi = KRML_HOST_CALLOC((size_t)32U, sizeof (uint8_t));
      __EngineTypes_engine_record_t_EngineTypes_dice_return_code
      ret = engine_main(cdi, vec_to_array__uint8_t(c), r);
      EngineTypes_engine_record_t
      r1 = fst__EngineTypes_engine_record_t_EngineTypes_dice_return_code(ret);
      KRML_MAYBE_UNUSED_VAR(r1);
      destroy_ctxt((
          (DPETypes_context_t){ .tag = DPETypes_Engine_context, { .case_Engine_context = c } }
        ));
      switch (snd__EngineTypes_engine_record_t_EngineTypes_dice_return_code(ret))
      {
        case DICE_SUCCESS:
          {
            uint8_t *l0_ctxt = init_l0_ctxt(cdi);
            return
              (
                (option__DPETypes_context_t){
                  .tag = FStar_Pervasives_Native_Some,
                  .v = { .tag = DPETypes_L0_context, { .case_L0_context = l0_ctxt } }
                }
              );
          }
        case DICE_ERROR:
          {
            zeroize((size_t)32U, cdi);
            return ((option__DPETypes_context_t){ .tag = FStar_Pervasives_Native_None });
          }
        default:
          {
            KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__, __LINE__);
            KRML_HOST_EXIT(253U);
          }
      }
    }
    else if (record.tag == DPETypes_L0_record)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (context.tag == DPETypes_L0_context)
  {
    uint8_t *c = context.case_L0_context;
    if (record.tag == DPETypes_L0_record)
    {
      L0Types_l0_record_t r = record.case_L0_record;
      uint8_t *deviceID_pub = alloc__uint8_t(0U, (size_t)32U);
      uint8_t *aliasKey_pub = alloc__uint8_t(0U, (size_t)32U);
      uint8_t *aliasKey_priv = alloc__uint8_t(0U, (size_t)32U);
      uint32_t deviceIDCSR_len = len_of_deviceIDCSR(r.deviceIDCSR_ingredients);
      uint32_t aliasKeyCRT_len = len_of_aliasKeyCRT(r.aliasKeyCRT_ingredients);
      uint8_t *deviceIDCSR = alloc__uint8_t(0U, (size_t)deviceIDCSR_len);
      uint8_t *aliasKeyCRT = alloc__uint8_t(0U, (size_t)aliasKeyCRT_len);
      L0Core_l0(vec_to_array__uint8_t(c),
        vec_to_array__uint8_t(r.fwid),
        r.deviceID_label_len,
        vec_to_array__uint8_t(r.deviceID_label),
        r.aliasKey_label_len,
        vec_to_array__uint8_t(r.aliasKey_label),
        r.deviceIDCSR_ingredients,
        r.aliasKeyCRT_ingredients,
        vec_to_array__uint8_t(deviceID_pub),
        vec_to_array__uint8_t(aliasKey_pub),
        vec_to_array__uint8_t(aliasKey_priv),
        deviceIDCSR_len,
        vec_to_array__uint8_t(deviceIDCSR),
        aliasKeyCRT_len,
        vec_to_array__uint8_t(aliasKeyCRT));
      DPETypes_l1_context_t
      l1_context =
        init_l1_ctxt(deviceID_pub,
          aliasKey_priv,
          aliasKey_pub,
          deviceIDCSR_len,
          deviceIDCSR,
          aliasKeyCRT_len,
          aliasKeyCRT);
      destroy_ctxt(((DPETypes_context_t){ .tag = DPETypes_L0_context, { .case_L0_context = c } }));
      return
        (
          (option__DPETypes_context_t){
            .tag = FStar_Pervasives_Native_Some,
            .v = { .tag = DPETypes_L1_context, { .case_L1_context = l1_context } }
          }
        );
    }
    else if (record.tag == DPETypes_Engine_record)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (context.tag == DPETypes_L1_context)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

bool DPE_derive_child(uint16_t sid, DPETypes_record_t record)
{
  DPE_session_state s = replace_session(sid, ((DPE_session_state){ .tag = DPE_InUse }));
  if (s.tag == DPE_Available)
  {
    DPETypes_context_t hc = s._0;
    if (hc.tag == DPETypes_L1_context)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else if (hc.tag == DPETypes_Engine_context)
    {
      option__DPETypes_context_t ret = derive_child_from_context(hc, record);
      if (ret.tag == FStar_Pervasives_Native_Some)
      {
        DPETypes_context_t nctxt = ret.v;
        DPE_session_state s1 = { .tag = DPE_Available, ._0 = nctxt };
        DPE_session_state s2 = replace_session(sid, s1);
        KRML_MAYBE_UNUSED_VAR(s2);
        return true;
      }
      else if (ret.tag == FStar_Pervasives_Native_None)
      {
        DPE_session_state s1 = { .tag = DPE_SessionError };
        DPE_session_state s2 = replace_session(sid, s1);
        KRML_MAYBE_UNUSED_VAR(s2);
        return false;
      }
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    else if (hc.tag == DPETypes_L0_context)
    {
      option__DPETypes_context_t ret = derive_child_from_context(hc, record);
      if (ret.tag == FStar_Pervasives_Native_Some)
      {
        DPETypes_context_t nctxt = ret.v;
        DPE_session_state s1 = { .tag = DPE_Available, ._0 = nctxt };
        DPE_session_state s2 = replace_session(sid, s1);
        KRML_MAYBE_UNUSED_VAR(s2);
        return true;
      }
      else if (ret.tag == FStar_Pervasives_Native_None)
      {
        DPE_session_state s1 = { .tag = DPE_SessionError };
        DPE_session_state s2 = replace_session(sid, s1);
        KRML_MAYBE_UNUSED_VAR(s2);
        return false;
      }
      else
      {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
          __FILE__,
          __LINE__,
          "unreachable (pattern matches are exhaustive in F*)");
        KRML_HOST_EXIT(255U);
      }
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (s.tag == DPE_SessionStart)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_InUse)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_SessionClosed)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_SessionError)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

static void destroy_session_state(DPE_session_state s)
{
  if (s.tag == DPE_Available)
  {
    DPETypes_context_t hc = s._0;
    destroy_ctxt(hc);
  }
  else if (!(s.tag == DPE_SessionStart))
    if (!(s.tag == DPE_InUse))
      if (!(s.tag == DPE_SessionClosed))
        if (!(s.tag == DPE_SessionError))
        {
          KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
            __FILE__,
            __LINE__,
            "unreachable (pattern matches are exhaustive in F*)");
          KRML_HOST_EXIT(255U);
        }
}

void DPE_close_session(uint16_t sid)
{
  DPE_session_state s = replace_session(sid, ((DPE_session_state){ .tag = DPE_InUse }));
  destroy_session_state(s);
  DPE_session_state s1 = replace_session(sid, ((DPE_session_state){ .tag = DPE_SessionClosed }));
  KRML_MAYBE_UNUSED_VAR(s1);
}

uint32_t DPE_certify_key(uint16_t sid, uint8_t *pub_key, uint32_t crt_len, uint8_t *crt)
{
  DPE_session_state s = replace_session(sid, ((DPE_session_state){ .tag = DPE_InUse }));
  if (s.tag == DPE_Available)
  {
    DPETypes_context_t hc = s._0;
    if (hc.tag == DPETypes_L1_context)
    {
      DPETypes_l1_context_t c = hc.case_L1_context;
      uint32_t c_crt_len = c.aliasKeyCRT_len;
      if (crt_len < c_crt_len)
      {
        DPE_session_state
        ns =
          { .tag = DPE_Available, ._0 = { .tag = DPETypes_L1_context, { .case_L1_context = c } } };
        DPE_session_state s1 = replace_session(sid, ns);
        KRML_MAYBE_UNUSED_VAR(s1);
        return 0U;
      }
      else
      {
        memcpy_l__uint8_t((size_t)32U, vec_to_array__uint8_t(c.aliasKey_pub), pub_key);
        memcpy_l__uint8_t((size_t)c.aliasKeyCRT_len, vec_to_array__uint8_t(c.aliasKeyCRT), crt);
        DPE_session_state
        ns =
          { .tag = DPE_Available, ._0 = { .tag = DPETypes_L1_context, { .case_L1_context = c } } };
        DPE_session_state s1 = replace_session(sid, ns);
        KRML_MAYBE_UNUSED_VAR(s1);
        return c_crt_len;
      }
    }
    else if (hc.tag == DPETypes_L0_context)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else if (hc.tag == DPETypes_Engine_context)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (s.tag == DPE_SessionStart)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_InUse)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_SessionClosed)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_SessionError)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

void DPE_sign(uint16_t sid, uint8_t *signature, size_t msg_len, uint8_t *msg)
{
  DPE_session_state s = replace_session(sid, ((DPE_session_state){ .tag = DPE_InUse }));
  if (s.tag == DPE_Available)
  {
    DPETypes_context_t hc = s._0;
    if (hc.tag == DPETypes_L1_context)
    {
      DPETypes_l1_context_t c = hc.case_L1_context;
      HACL_ed25519_sign(signature, vec_to_array__uint8_t(c.aliasKey_priv), msg_len, msg);
      DPE_session_state
      ns = { .tag = DPE_Available, ._0 = { .tag = DPETypes_L1_context, { .case_L1_context = c } } };
      DPE_session_state s1 = replace_session(sid, ns);
      KRML_MAYBE_UNUSED_VAR(s1);
    }
    else if (hc.tag == DPETypes_L0_context)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else if (hc.tag == DPETypes_Engine_context)
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "Pulse.Lib.Dv.unreachable");
      KRML_HOST_EXIT(255U);
    }
    else
    {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
        __FILE__,
        __LINE__,
        "unreachable (pattern matches are exhaustive in F*)");
      KRML_HOST_EXIT(255U);
    }
  }
  else if (s.tag == DPE_SessionStart)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_InUse)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_SessionClosed)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else if (s.tag == DPE_SessionError)
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "Pulse.Lib.Dv.unreachable");
    KRML_HOST_EXIT(255U);
  }
  else
  {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

