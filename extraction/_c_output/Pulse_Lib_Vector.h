#ifndef Pulse_Lib_Vector_H
#define Pulse_Lib_Vector_H
#include "Pulse_Lib_RangeVec.h"

typedef Pulse_Lib_RangeVec_range range_t_;
typedef Pulse_Lib_Vector_vector_internal__Pulse_Lib_RangeVec_range vec_t_;

extern vec_t_ *Pulse_Lib_Vector_create(range_t_ def, size_t n);
extern void Pulse_Lib_Vector_free(vec_t_ *v, void *_s, void *_cap);
extern range_t_ Pulse_Lib_Vector_at(vec_t_ *v, size_t i, void *_s, void *_cap);
extern void Pulse_Lib_Vector_set(vec_t_ *v, size_t i, range_t_ x, void *_s, void *_cap);
extern size_t Pulse_Lib_Vector_size(vec_t_ *v, void *_s, void *_cap);
extern void Pulse_Lib_Vector_push_back(vec_t_ *v, range_t_ x, void *_s, void *_cap);
extern range_t_ Pulse_Lib_Vector_pop_back(vec_t_ *v, void *_s, void *_cap);

#endif
