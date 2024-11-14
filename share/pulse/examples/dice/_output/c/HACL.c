
#include "HACL.h"

extern void EverCrypt_AutoConfig2_init(void);

extern void
EverCrypt_Ed25519_sign(
  uint8_t *signature,
  uint8_t *private_key,
  uint32_t msg_len,
  uint8_t *msg
);

extern bool
EverCrypt_Ed25519_verify(
  uint8_t *public_key,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *signature
);

extern Spec_Hash_Definitions_hash_alg Spec_Hash_Definitions_sha2_256;

extern uint32_t EverCrypt_Hash_Incremental_hash_len(Spec_Hash_Definitions_hash_alg a);

extern void
EverCrypt_Hash_Incremental_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len
);

extern void
EverCrypt_HMAC_compute(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *x0,
  uint8_t *x1,
  uint32_t x2,
  uint8_t *x3,
  uint32_t x4
);

size_t HACL_digest_len(Spec_Hash_Definitions_hash_alg a)
{
  return (size_t)EverCrypt_Hash_Incremental_hash_len(a);
}

static void
hacl_hash0(Spec_Hash_Definitions_hash_alg alg, size_t src_len, uint8_t *src, uint8_t *dst)
{
  EverCrypt_AutoConfig2_init();
  EverCrypt_Hash_Incremental_hash(alg, dst, src, (uint32_t)src_len);
}

void
(*HACL_hacl_hash)(Spec_Hash_Definitions_hash_alg x0, size_t x1, uint8_t *x2, uint8_t *x3) =
  hacl_hash0;

static void
hacl_hmac0(
  Spec_Hash_Definitions_hash_alg alg,
  uint8_t *dst,
  uint8_t *key,
  size_t key_len,
  uint8_t *msg,
  size_t msg_len
)
{
  EverCrypt_HMAC_compute(alg, dst, key, (uint32_t)key_len, msg, (uint32_t)msg_len);
}

void
(*HACL_hacl_hmac)(
  Spec_Hash_Definitions_hash_alg x0,
  uint8_t *x1,
  uint8_t *x2,
  size_t x3,
  uint8_t *x4,
  size_t x5
) = hacl_hmac0;

static bool ed25519_verify0(uint8_t *pubk, uint8_t *hdr, size_t hdr_len, uint8_t *sig)
{
  return EverCrypt_Ed25519_verify(pubk, (uint32_t)hdr_len, hdr, sig);
}

bool
(*HACL_ed25519_verify)(uint8_t *x0, uint8_t *x1, size_t x2, uint8_t *x3) = ed25519_verify0;

static void ed25519_sign0(uint8_t *buf, uint8_t *privk, size_t len, uint8_t *msg)
{
  EverCrypt_Ed25519_sign(buf, privk, (uint32_t)len, msg);
}

void (*HACL_ed25519_sign)(uint8_t *x0, uint8_t *x1, size_t x2, uint8_t *x3) = ed25519_sign0;

static Spec_Hash_Definitions_hash_alg dice_hash_alg1(void)
{
  return Spec_Hash_Definitions_sha2_256;
}

Spec_Hash_Definitions_hash_alg HACL_dice_hash_alg0(void)
{
  return dice_hash_alg1();
}

