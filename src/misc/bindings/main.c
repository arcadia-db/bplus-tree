#include "main.h"

int main() {
    // Make sure to allocate (string_len + 1) for strings for null-terminator.

    const char *namespace_ptr = (char *)calloc(6 + 1, sizeof(char));
    strcpy(namespace_ptr, "normal");

    uint8_t *uuid_ptr = (uint8_t *)calloc(0x10, sizeof(uint8_t));
    for (int i = 0; i < 0x10; ++i) {
        uuid_ptr[i] = i + 0x10;
    }

    const char *kind_ptr = (char *)calloc(4 + 1, sizeof(char));
    strcpy(kind_ptr, "test");

    const uint64_t body_len = 2;
    uint8_t *body_ptr = (uint8_t *)calloc(body_len, sizeof(uint8_t));
    body_ptr[0] = 23;
    body_ptr[1] = 0x23;

    // Prints no messages
    print_messages();
    printf("\n\n\n");

    // Pass message to Rust
    const bool result1 = pass_message(
        namespace_ptr,
        uuid_ptr,
        kind_ptr,
        body_len,
        body_ptr
    );
    printf("%i", result1);

    // Should print the previous passed message
    print_messages();
    printf("\n\n\n");

    // Send the same message
    const bool result2 = pass_message(
        namespace_ptr,
        uuid_ptr,
        kind_ptr,
        body_len,
        body_ptr
    );
    printf("%i", result2);

    // Should print two of the same message from earlier
    print_messages();
    printf("\n\n\n");

    // To show that Rust owns the data, not C, we modify the data and resend.
    strcpy(namespace_ptr, "asdfqw");
    for (int i = 0; i < 0x10; ++i) {
        uuid_ptr[i] = i + 0x20;
    }
    strcpy(kind_ptr, "asdf");
    body_ptr[0] = 54;
    body_ptr[1] = 0x54;
    const bool result3 = pass_message(
        namespace_ptr,
        uuid_ptr,
        kind_ptr,
        body_len,
        body_ptr
    );
    printf("%i", result3);

    // Should print two of the old message and one new
    print_messages();
    printf("\n\n\n");

    // Frees the data in C. Rust should still own the data.
    free(namespace_ptr);
    free(uuid_ptr);
    free(kind_ptr);
    free(body_ptr);

    // Should still print properly in Rust
    print_messages();
    printf("\n\n\n");

    // Passing in garbage data
    const bool result4 = pass_message(
        namespace_ptr,
        uuid_ptr,
        kind_ptr,
        body_len,
        body_ptr
    );
    printf("%i", result4);

    // Should show all previous messages correctly, then one garbage message
    print_messages();
    printf("\n\n\n");

    return EXIT_SUCCESS;
}
