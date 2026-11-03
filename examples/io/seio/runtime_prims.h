#include "gc_stack.h"
value io_read(struct thread_info *ti, value fd);
value io_write(struct thread_info *ti, value fd_msg);
value io_open(struct thread_info *ti, value name);
value io_close(struct thread_info *ti, value fd);
