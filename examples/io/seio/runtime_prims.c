/* The SEIO* operations of Runtime.v for the CertiRocq C backend.  Values:
   nat O is the constant 1 and S n a one-field block of tag 0; inl x and inr x
   are one-field blocks of tags 0 and 1; tt is the constant 1; a pair is a
   two-field block of tag 0; a string is a block of tag 252 laid out as an
   OCaml string.  All four primitives allocate, so their remaps set
   re_const_gc. */
#include <stdio.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include "gc_stack.h"
#include "values.h"
#include "runtime_prims.h"

#define String_tag 252
#define UNIT ((value) 1)

static long nat_val(value n)
{
  long k = 0;
  while (!Is_long(n)) { n = Field(n, 0); k++; }
  return k;
}

/* Make room for [words] words, collecting first if needed.  No value
   allocated by the caller may be live across this call. */
static value *reserve(struct thread_info *ti, unsigned long words)
{
  if (!(words <= (unsigned long) (ti->limit - ti->alloc))) {
    ti->nalloc = words;
    garbage_collect(ti);
  }
  return ti->alloc;
}

static value block1(struct thread_info *ti, unsigned tag, value x)
{
  value *p = ti->alloc;
  p[0] = (1 << 10) | tag;
  p[1] = x;
  ti->alloc += 2;
  return (value) (p + 1);
}

static value string_val(struct thread_info *ti, const char *s, unsigned long len)
{
  unsigned long words = len / 8 + 1;
  value *p = ti->alloc;
  p[0] = String_tag | (words << 10);
  char *b = (char *) (p + 1);
  memcpy(b, s, len);
  unsigned long j = len;
  for (; (j + 1) / 8 < words; j++) b[j] = 0;
  b[j] = (char) (j - len);
  ti->alloc += words + 1;
  return (value) (p + 1);
}

static unsigned long string_len(value s)
{
  unsigned long n = Bosize_val(s) - 1;
  return n - Byte(s, n);
}

/* As SEIO*'s realization: read to the end of the file, and fail only when the
   descriptor cannot be read. */
value io_read(struct thread_info *ti, value fd)
{
  static char buf[1 << 20];
  long len = 0;
  ssize_t got = 0;
  int fdn = (int) nat_val(fd);
  while (len < (long) sizeof buf && (got = read(fdn, buf + len, sizeof buf - len)) > 0) len += got;
  if (len == 0 && got < 0) { reserve(ti, 2); return block1(ti, 1, UNIT); }
  reserve(ti, len / 8 + 2 + 2);
  return block1(ti, 0, string_val(ti, buf, len));
}

value io_write(struct thread_info *ti, value fd_msg)
{
  int fdn = (int) nat_val(Field(fd_msg, 0));
  value msg = Field(fd_msg, 1);
  unsigned long len = string_len(msg);
  int ok = write(fdn, (char *) msg, len) == (ssize_t) len;
  reserve(ti, 2);
  return block1(ti, ok ? 0 : 1, UNIT);
}

value io_open(struct thread_info *ti, value name)
{
  char path[4096];
  unsigned long len = string_len(name);
  if (len >= sizeof path) { reserve(ti, 2); return block1(ti, 1, UNIT); }
  memcpy(path, (char *) name, len); path[len] = 0;
  int fd = open(path, O_RDWR | O_CREAT, 0644);
  if (fd < 0) { reserve(ti, 2); return block1(ti, 1, UNIT); }
  value *p = reserve(ti, 2 * (unsigned long) fd + 2);
  (void) p;
  value n = (value) 1;
  for (int i = 0; i < fd; i++) n = block1(ti, 0, n);
  return block1(ti, 0, n);
}

value io_close(struct thread_info *ti, value fd)
{
  int ok = close((int) nat_val(fd)) == 0;
  reserve(ti, 2);
  return block1(ti, ok ? 0 : 1, UNIT);
}
