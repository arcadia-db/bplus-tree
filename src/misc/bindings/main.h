#ifndef MAIN_H
#define MAIN_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

extern void print_messages();

extern bool pass_message(
    const char *const namespace_ptr,
    const uint8_t *const uuid_ptr,
    const char *const kind_ptr,
    const uint64_t body_len,
    const uint8_t *const body_ptr
);

#endif // MAIN_H
