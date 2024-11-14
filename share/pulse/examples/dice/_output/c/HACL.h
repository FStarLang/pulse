
#ifndef __HACL_H
#define __HACL_H

#include "krmllib.h"

#include "Pulse_Lib_SpinLock.h"
#include "EverCrypt_Base.h"

typedef Spec_Hash_Definitions_hash_alg HACL_alg_t;

size_t HACL_digest_len(Spec_Hash_Definitions_hash_alg a);

typedef void *HACL_is_hashable_len;

typedef size_t HACL_hashable_len;

typedef void *HACL_is_signable_len;

typedef size_t HACL_signable_len;

typedef void *HACL_valid_hkdf_lbl_len;

typedef size_t HACL_hkdf_lbl_len;

typedef void *HACL_valid_hkdf_ikm_len;

typedef size_t HACL_hkdf_ikm_len;

extern void
(*HACL_hacl_hash)(Spec_Hash_Definitions_hash_alg x0, size_t x1, uint8_t *x2, uint8_t *x3);

extern void
(*HACL_hacl_hmac)(
  Spec_Hash_Definitions_hash_alg x0,
  uint8_t *x1,
  uint8_t *x2,
  size_t x3,
  uint8_t *x4,
  size_t x5
);

typedef void *HACL_spec_ed25519_verify;

extern bool (*HACL_ed25519_verify)(uint8_t *x0, uint8_t *x1, size_t x2, uint8_t *x3);

extern void (*HACL_ed25519_sign)(uint8_t *x0, uint8_t *x1, size_t x2, uint8_t *x3);

Spec_Hash_Definitions_hash_alg HACL_dice_hash_alg0(void);


#define __HACL_H_DEFINED
#endif
