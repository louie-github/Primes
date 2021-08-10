# Solution based on PrimeRust/solution_1 (FlagStorageBitVectorStripedBlocks)
# by Michael Barber (@mike-barber).

module PrimesStriped
export PrimeSieveStripedBlocks

import ..PrimesSolution3

const MainUInt = UInt8
const UINT_BIT_LENGTH = sizeof(MainUInt) * 8
const BLOCK_SIZE = 16 * 1024
const BLOCK_SIZE_BITS = BLOCK_SIZE * UINT_BIT_LENGTH

@inline _mul2(i::Integer) = i << 1
@inline _div2(i::Integer) = i >> 1
@inline _map_to_index(i::Integer) = _div2(i - 1)
@inline _map_to_factor(i::Integer) = _mul2(i) + 1
# This is more accurate than _div_uint_size(_div2(i)) + 1
# We only store odd numbers starting from 3, so we subtract 2 from i
# to account for that.
@inline function _get_num_blocks(i::Integer)
    return (i - 2 + (2 * BLOCK_SIZE_BITS - 1)) ÷ 2 ÷ BLOCK_SIZE_BITS
end


struct PrimeSieveStripedBlocks <: PrimesSolution3.AbstractPrimeSieve
    sieve_size::UInt
    length_bits::UInt
    blocks::Vector{Vector{MainUInt}}
end


function PrimeSieveStripedBlocks(sieve_size::UInt)
    return PrimeSieveStripedBlocks(
        sieve_size,
        _map_to_index(sieve_size),
        [fill(typemax(MainUInt), BLOCK_SIZE) for _ in 1:_get_num_blocks(sieve_size)]
    )
end

# The main() function uses the UInt constructor; this is mostly useful
# for testing in the REPL.
PrimeSieveStripedBlocks(sieve_size::Int) = PrimeSieveStripedBlocks(UInt(sieve_size))

@inline function unsafe_get_bit_at_zero_index(
    sieve::PrimeSieveStripedBlocks, index::Integer
)
    if index >= sieve.length_bits
        return false
    end
    block_index = index ÷ BLOCK_SIZE_BITS
    offset = index % BLOCK_SIZE_BITS
    bit_index = offset ÷ BLOCK_SIZE
    word_index = offset % BLOCK_SIZE
    word = @inbounds sieve.blocks[block_index + 1][word_index + 1]
    return !iszero(word & (1 << bit_index))
end

@inline unsafe_get_bit_at_index(
    sieve::PrimeSieveStripedBlocks, index::Integer
) = unsafe_get_bit_at_zero_index(sieve, index - 1)

@inline function PrimesSolution3.unsafe_find_next_factor_index(
    sieve::PrimeSieveStripedBlocks,
    start_index::Integer,
    max_index::Integer
)
    # This loop calculates indices as if they are zero-based then adds
    # 1 when accessing the array since Julia uses 1-based indexing.
    zero_index = start_index
    @inbounds while zero_index < max_index
        if unsafe_get_bit_at_zero_index(sieve, zero_index)
            return zero_index + 1
        end
        zero_index += 1
    end
    # UNSAFE: you need to check this in the caller or make sure it
    # never happens
    return max_index + 1
end

@inline function PrimesSolution3.unsafe_clear_factors!(
    sieve::PrimeSieveStripedBlocks,
    factor_index::Integer
)
    factor = _map_to_factor(factor_index)
    start = factor * factor ÷ 2 - 1
    skip = factor
    skip > BLOCK_SIZE && error("skip > BLOCK_SIZE; unsupported")

    blocks = sieve.blocks
    num_blocks = length(blocks)
    block_idx = start ÷ BLOCK_SIZE_BITS
    offset_idx = start % BLOCK_SIZE_BITS
    bit_idx = offset_idx ÷ BLOCK_SIZE
    word_idx = offset_idx % BLOCK_SIZE

    # Variables for unrolling loop
    skip2 = skip * 2
    skip3 = skip * 3
    skip4 = skip * 4
    BLOCK_SIZE_MINUS_SKIP3 = BLOCK_SIZE - skip3

    @inbounds while block_idx < num_blocks
        block = blocks[block_idx + 1]
        while bit_idx < UINT_BIT_LENGTH
            # Calculate length of current stripe, if it is less than
            # BLOCK_SIZE, then we know that this should be the last
            # iteration.
            # For some reason, 1 << bit_idx is faster than
            # MainUInt(1) << bit_idx.
            mask = ~(1 << bit_idx)
            stripe_start_position = block_idx * BLOCK_SIZE_BITS + bit_idx * BLOCK_SIZE
            effective_len = sieve.length_bits - stripe_start_position
            # Last iteration
            if effective_len < BLOCK_SIZE
                unrolled_end_index = effective_len - skip3
                if !(unrolled_end_index < effective_len)
                    unrolled_end_index = 0
                end
                while word_idx < unrolled_end_index
                    block[word_idx + 1] &= mask
                    block[word_idx + skip + 1] &= mask
                    block[word_idx + skip2 + 1] &= mask
                    block[word_idx + skip3 + 1] &= mask
                    word_idx += skip4
                end
                while word_idx < effective_len
                    block[word_idx + 1] &= mask
                    word_idx += skip
                end
                return
            else
                while word_idx < BLOCK_SIZE_MINUS_SKIP3
                    block[word_idx + 1] &= mask
                    block[word_idx + skip + 1] &= mask
                    block[word_idx + skip2 + 1] &= mask
                    block[word_idx + skip3 + 1] &= mask
                    word_idx += skip4
                end
                while word_idx < BLOCK_SIZE
                    block[word_idx + 1] &= mask
                    word_idx += skip
                end
            end
            bit_idx += 1
            word_idx -= BLOCK_SIZE
        end
        bit_idx = 0
        block_idx += 1
    end
end

function PrimesSolution3.run_sieve!(sieve::PrimeSieveStripedBlocks)
    max_factor_index = _map_to_index(
        unsafe_trunc(UInt, sqrt(sieve.sieve_size))
    )
    factor_index = UInt(1) # 1 => 3, 2 => 5, 3 => 7, ...
    while factor_index <= max_factor_index
        PrimesSolution3.unsafe_clear_factors!(sieve, factor_index)
        factor_index = PrimesSolution3.unsafe_find_next_factor_index(
            sieve, factor_index, max_factor_index
        )
    end
    return sieve
end


# These functions aren't optimized, but they aren't being benchmarked,
# so it's fine.

function PrimesSolution3.count_primes(sieve::PrimeSieveStripedBlocks)
    # Since we start clearing factors at 3, we include 2 in the count
    # beforehand.
    count = 1
    for i in 1:sieve.length_bits
        if unsafe_get_bit_at_index(sieve, i)
            count += 1
        end
    end
    return count
end

function PrimesSolution3.get_found_primes(sieve::PrimeSieveStripedBlocks)
    output = [2]
    # Int(sieve_size) may overflow if sieve_size is too large (most
    # likely only a problem for 32-bit systems)
    for (index, number) in zip(1:sieve.length_bits, 3:2:Int(sieve.sieve_size))
        if unsafe_get_bit_at_index(sieve, index)
            push!(output, number)
        end
    end
    return output
end

end
