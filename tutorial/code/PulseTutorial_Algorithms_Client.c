/* krml header omitted for test repeatability */


#include "PulseTutorial_Algorithms_Client.h"

/* SNIPPET_START: option__uint32_t_tags */

#define None 0
#define Some 1

/* SNIPPET_END: option__uint32_t_tags */

typedef uint8_t option__uint32_t_tags;

/* SNIPPET_START: option__uint32_t */

typedef struct option__uint32_t_s
{
  option__uint32_t_tags tag;
  uint32_t v;
}
option__uint32_t;

/* SNIPPET_END: option__uint32_t */

/* SNIPPET_START: majority__uint32_t */

static option__uint32_t majority__uint32_t(uint32_t *votes, size_t len)
{
  size_t i = (size_t)1U;
  size_t k = (size_t)1U;
  uint32_t votes_0 = votes[0U];
  uint32_t cand = votes_0;
  size_t __anf00 = i;
  bool cond = __anf00 < len;
  while (cond)
  {
    size_t vi = i;
    size_t vk = k;
    uint32_t vcand = cand;
    uint32_t votes_i = votes[vi];
    if (vk == (size_t)0U)
    {
      cand = votes_i;
      k = (size_t)1U;
      i = vi + (size_t)1U;
    }
    else if (votes_i == vcand)
    {
      k = vk + (size_t)1U;
      i = vi + (size_t)1U;
    }
    else
    {
      k = vk - (size_t)1U;
      i = vi + (size_t)1U;
    }
    size_t __anf0 = i;
    cond = __anf0 < len;
  }
  size_t vk = k;
  uint32_t vcand = cand;
  if (vk == (size_t)0U)
    return ((option__uint32_t){ .tag = None });
  else if (len < (size_t)2U * vk)
    return ((option__uint32_t){ .tag = Some, .v = vcand });
  else
  {
    i = (size_t)0U;
    k = (size_t)0U;
    size_t __anf0 = i;
    bool cond = __anf0 < len;
    while (cond)
    {
      size_t vi = i;
      size_t vk1 = k;
      uint32_t votes_i = votes[vi];
      if (votes_i == vcand)
      {
        k = vk1 + (size_t)1U;
        i = vi + (size_t)1U;
      }
      else
        i = vi + (size_t)1U;
      size_t __anf0 = i;
      cond = __anf0 < len;
    }
    size_t vk1 = k;
    if (len < (size_t)2U * vk1)
      return ((option__uint32_t){ .tag = Some, .v = vcand });
    else
      return ((option__uint32_t){ .tag = None });
  }
}

/* SNIPPET_END: majority__uint32_t */

/* SNIPPET_START: main */

int32_t main(void)
{
  uint32_t votes[4U];
  memset(votes, 0U, (size_t)4U * sizeof (uint32_t));
  votes[0U] = 1U;
  votes[1U] = 1U;
  votes[2U] = 0U;
  votes[3U] = 1U;
  option__uint32_t __anf0 = majority__uint32_t(votes, (size_t)4U);
  if (__anf0.tag == None)
  {
    puts("No majority\n");
    return (int32_t)0;
  }
  else if (__anf0.tag == Some)
  {
    uint32_t v = __anf0.v;
    printf("Majority: %d\n", v);
    return (int32_t)0;
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

/* SNIPPET_END: main */

