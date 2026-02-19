#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <stddef.h>

/* Pulse.Lib.Array.memcpy_l — copy `n` elements from src to dst */
void Pulse_Lib_Array_memcpy_l(size_t n, void* src, void* dst,
                               void* p1, void* p2, void* p3) {
    /* Each element is a Pulse_Lib_RangeVec_range = {size_t, size_t} = 2*sizeof(size_t) */
    memcpy(dst, src, n * 2 * sizeof(size_t));
}
