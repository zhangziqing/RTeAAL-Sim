#pragma once
#include <cstdint>

// Opcode 29: [N, source0, offset0, ..., sourceN-1, offsetN-1]. Offsets
// are immediate bit positions; sources are data slots. The compiler preserves
// high-to-low field order and emits scalar results of at most 64 bits.
template<class Cursor>
inline uint64_t concatn_value(Cursor& args, const uint64_t* data) {
    const uint32_t count = *args++;
    uint64_t result = 0;
    for (uint32_t i = 0; i < count; ++i) {
        const uint32_t source = *args++;
        const uint32_t offset = *args++;
        result |= offset < 64 ? data[source] << offset : 0;
    }
    return result;
}
