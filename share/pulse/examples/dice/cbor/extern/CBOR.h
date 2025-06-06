/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /home/tahina/everest/steel/karamel/krml -bundle C -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Constants,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CBOR.Pulse= -bundle CDDLExtractionTest.Assume+CDDLExtractionTest.Bytes+CDDLExtractionTest.BytesUnwrapped+CDDLExtractionTest.Choice=*[rename=CDDLExtractionTest] -skip-linking _output/FStar_Pervasives_Native.krml _output/FStar_Pervasives.krml _output/FStar_Mul.krml _output/FStar_Squash.krml _output/FStar_Classical.krml _output/FStar_Preorder.krml _output/FStar_Sealed.krml _output/FStar_Range.krml _output/FStar_Calc.krml _output/FStar_StrongExcludedMiddle.krml _output/FStar_Classical_Sugar.krml _output/FStar_List_Tot_Base.krml _output/FStar_List_Tot_Properties.krml _output/FStar_List_Tot.krml _output/FStar_Seq_Base.krml _output/FStar_Seq_Properties.krml _output/FStar_Seq.krml _output/FStar_Math_Lib.krml _output/FStar_Math_Lemmas.krml _output/FStar_BitVector.krml _output/FStar_UInt.krml _output/FStar_UInt32.krml _output/FStar_Int.krml _output/FStar_Int16.krml _output/FStar_Int64.krml _output/FStar_Int32.krml _output/FStar_Int8.krml _output/FStar_UInt64.krml _output/FStar_UInt16.krml _output/FStar_UInt8.krml _output/FStar_Int_Cast.krml _output/FStar_Ghost.krml _output/FStar_SizeT.krml _output/FStar_Float.krml _output/FStar_Char.krml _output/FStar_Pprint.krml _output/FStar_Issue.krml _output/FStar_TypeChecker_Core.krml _output/FStar_Tactics_Common.krml _output/FStar_Reflection_Types.krml _output/FStar_Tactics_Types.krml _output/FStar_Tactics_Result.krml _output/FStar_Monotonic_Pure.krml _output/FStar_VConfig.krml _output/FStar_Sealed_Inhabited.krml _output/FStar_Syntax_Syntax.krml _output/FStar_Reflection_V2_Data.krml _output/FStar_Order.krml _output/FStar_Reflection_V2_Builtins.krml _output/FStar_Tactics_V2_Builtins.krml _output/FStar_PropositionalExtensionality.krml _output/FStar_Reflection_V1_Data.krml _output/FStar_Reflection_V1_Builtins.krml _output/FStar_Tactics_V1_Builtins.krml _output/FStar_IndefiniteDescription.krml _output/FStar_Algebra_CommMonoid.krml _output/FStar_Exn.krml _output/FStar_FunctionalExtensionality.krml _output/FStar_Set.krml _output/FStar_Monotonic_Witnessed.krml _output/FStar_ErasedLogic.krml _output/FStar_PredicateExtensionality.krml _output/FStar_TSet.krml _output/FStar_Monotonic_Heap.krml _output/FStar_Heap.krml _output/FStar_ST.krml _output/FStar_All.krml _output/FStar_List.krml _output/FStar_Universe.krml _output/FStar_Witnessed_Core.krml _output/FStar_MSTTotal.krml _output/FStar_NMSTTotal.krml _output/FStar_PCM.krml _output/FStar_Real.krml _output/FStar_WellFounded.krml _output/FStar_MST.krml _output/FStar_NMST.krml _output/FStar_String.krml _output/FStar_Algebra_CommMonoid_Equiv.krml _output/Pulse_Lib_Reference.krml _output/Pulse_Lib_BoundedIntegers.krml _output/FStar_Map.krml _output/FStar_PtrdiffT.krml _output/Pulse_Lib_Array_Core.krml _output/FStar_Int128.krml _output/FStar_BV.krml _output/FStar_UInt128.krml _output/FStar_Integers.krml _output/FStar_Printf.krml _output/Pulse_Lib_Array.krml _output/Pulse_Lib_Pervasives.krml _output/Pulse_Lib_ArraySwap.krml _output/Pulse_Lib_Trade.krml _output/Pulse_Lib_SeqMatch.krml _output/CBOR_Spec_Constants.krml _output/CBOR_Spec_Type.krml _output/CBOR_Spec_Map.krml _output/CBOR_Spec.krml _output/CBOR_Pulse_Type.krml _output/CBOR_Pulse_Extern.krml _output/CBOR_Pulse.krml _output/FStar_Ghost_Pull.krml _output/CDDL_Spec.krml _output/CDDL_Pulse.krml _output/CDDLExtractionTest_Assume.krml _output/CDDLExtractionTest_Choice.krml _output/CDDLExtractionTest_BytesVeryDirect.krml _output/CDDLExtractionTest_BytesUnwrapped.krml _output/CDDLExtractionTest_BytesVeryDirectFail.krml _output/CDDLExtractionTest_Bytes.krml _output/CDDLExtractionTest_BytesDirect.krml -tmpdir _output
  F* version: b67ab328
  KaRaMeL version: 0644e20d
 */

#ifndef __CBOR_H
#define __CBOR_H

#include "krmllib.h"

#define CBOR_MAJOR_TYPE_SIMPLE_VALUE (7U)

#define CBOR_MAJOR_TYPE_UINT64 (0U)

#define CBOR_MAJOR_TYPE_NEG_INT64 (1U)

#define CBOR_MAJOR_TYPE_BYTE_STRING (2U)

#define CBOR_MAJOR_TYPE_TEXT_STRING (3U)

#define CBOR_MAJOR_TYPE_ARRAY (4U)

#define CBOR_MAJOR_TYPE_MAP (5U)

#define CBOR_MAJOR_TYPE_TAGGED (6U)

typedef struct cbor_int_s
{
  uint8_t cbor_int_type;
  uint64_t cbor_int_value;
}
cbor_int;

typedef struct cbor_string_s
{
  uint8_t cbor_string_type;
  uint64_t cbor_string_length;
  uint8_t *cbor_string_payload;
}
cbor_string;

typedef struct cbor_serialized_s
{
  size_t cbor_serialized_size;
  uint8_t *cbor_serialized_payload;
}
cbor_serialized;

typedef struct cbor_s cbor;

typedef struct cbor_s cbor;

typedef struct cbor_tagged0_s
{
  uint64_t cbor_tagged0_tag;
  cbor *cbor_tagged0_payload;
}
cbor_tagged0;

typedef struct cbor_s cbor;

typedef struct cbor_s cbor;

typedef struct cbor_array_s
{
  uint64_t cbor_array_length;
  cbor *cbor_array_payload;
}
cbor_array;

typedef struct cbor_map_entry_s cbor_map_entry;

typedef struct cbor_map_s
{
  uint64_t cbor_map_length;
  cbor_map_entry *cbor_map_payload;
}
cbor_map;

#define CBOR_Case_Int64 0
#define CBOR_Case_String 1
#define CBOR_Case_Tagged 2
#define CBOR_Case_Array 3
#define CBOR_Case_Map 4
#define CBOR_Case_Simple_value 5
#define CBOR_Case_Serialized 6

typedef uint8_t cbor_tags;

typedef struct cbor_s
{
  cbor_tags tag;
  union {
    cbor_int case_CBOR_Case_Int64;
    cbor_string case_CBOR_Case_String;
    cbor_tagged0 case_CBOR_Case_Tagged;
    cbor_array case_CBOR_Case_Array;
    cbor_map case_CBOR_Case_Map;
    uint8_t case_CBOR_Case_Simple_value;
    cbor_serialized case_CBOR_Case_Serialized;
  }
  ;
}
cbor;

typedef struct cbor_map_entry_s
{
  cbor cbor_map_entry_key;
  cbor cbor_map_entry_value;
}
cbor_map_entry;

#define CBOR_Array_Iterator_Payload_Array 0
#define CBOR_Array_Iterator_Payload_Serialized 1

typedef uint8_t cbor_array_iterator_payload_t_tags;

typedef struct cbor_array_iterator_payload_t_s
{
  cbor_array_iterator_payload_t_tags tag;
  union {
    cbor *case_CBOR_Array_Iterator_Payload_Array;
    uint8_t *case_CBOR_Array_Iterator_Payload_Serialized;
  }
  ;
}
cbor_array_iterator_payload_t;

typedef struct cbor_array_iterator_t_s
{
  uint64_t cbor_array_iterator_length;
  cbor_array_iterator_payload_t cbor_array_iterator_payload;
}
cbor_array_iterator_t;

#define CBOR_Map_Iterator_Payload_Map 0
#define CBOR_Map_Iterator_Payload_Serialized 1

typedef uint8_t cbor_map_iterator_payload_t_tags;

typedef struct cbor_map_iterator_payload_t_s
{
  cbor_map_iterator_payload_t_tags tag;
  union {
    cbor_map_entry *case_CBOR_Map_Iterator_Payload_Map;
    uint8_t *case_CBOR_Map_Iterator_Payload_Serialized;
  }
  ;
}
cbor_map_iterator_payload_t;

typedef struct cbor_map_iterator_t_s
{
  uint64_t cbor_map_iterator_length;
  cbor_map_iterator_payload_t cbor_map_iterator_payload;
}
cbor_map_iterator_t;

extern cbor cbor_dummy;

extern cbor cbor_map_entry_key(cbor_map_entry uu___);

extern cbor cbor_map_entry_value(cbor_map_entry uu___);

extern cbor_map_entry cbor_mk_map_entry(cbor key, cbor value);

typedef struct cbor_read_t_s
{
  bool cbor_read_is_success;
  cbor cbor_read_payload;
  uint8_t *cbor_read_remainder;
  size_t cbor_read_remainder_length;
}
cbor_read_t;

extern cbor_read_t cbor_read(uint8_t *a, size_t sz);

extern cbor_read_t cbor_read_deterministically_encoded(uint8_t *a, size_t sz);

extern cbor_int cbor_destr_int64(cbor c);

extern cbor cbor_constr_int64(uint8_t ty, uint64_t value);

extern uint8_t cbor_destr_simple_value(cbor c);

extern cbor cbor_constr_simple_value(uint8_t value);

extern cbor_string cbor_destr_string(cbor c);

extern cbor cbor_constr_string(uint8_t typ, uint8_t *a, uint64_t len);

extern cbor cbor_constr_array(cbor *a, uint64_t len);

extern uint64_t cbor_array_length(cbor a);

extern cbor cbor_array_index(cbor a, size_t i);

extern cbor_array_iterator_t cbor_dummy_array_iterator;

extern cbor_array_iterator_t cbor_array_iterator_init(cbor a);

extern bool cbor_array_iterator_is_done(cbor_array_iterator_t i);

extern cbor cbor_array_iterator_next(cbor_array_iterator_t *pi);

extern cbor *cbor_read_array(cbor a, cbor *dest, uint64_t len);

typedef struct cbor_tagged_s
{
  uint64_t cbor_tagged_tag;
  cbor cbor_tagged_payload;
}
cbor_tagged;

extern cbor_tagged cbor_destr_tagged(cbor a);

extern cbor cbor_constr_tagged(uint64_t tag, cbor *a);

extern cbor cbor_constr_map(cbor_map_entry *a, uint64_t len);

extern uint64_t cbor_map_length(cbor a);

extern cbor_map_iterator_t cbor_dummy_map_iterator;

extern cbor_map_iterator_t cbor_map_iterator_init(cbor a);

extern bool cbor_map_iterator_is_done(cbor_map_iterator_t i);

extern cbor_map_entry cbor_map_iterator_next(cbor_map_iterator_t *pi);

extern uint8_t cbor_get_major_type(cbor a);

extern int16_t cbor_compare_aux(cbor c1, cbor c2);

extern size_t cbor_write(cbor c, uint8_t *out, size_t sz);


#define __CBOR_H_DEFINED
#endif
