
#include "krmlinit.h"

#include "internal/DPE.h"

#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif

void krmlinit_globals(void)
{
  DPE_gst = DPE_initialize_global_state();
}

