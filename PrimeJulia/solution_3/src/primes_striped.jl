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
    return (i - 2 + (2 * BLOCK_SIZE_BITS - 1)) ÷ TWO ÷ BLOCK_SIZE_BITS
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
        [zeros(MainUInt, BLOCK_SIZE) for _ in 1:_get_num_blocks(sieve_size)]
    )
end

# The main() function uses the UInt constructor; this is mostly useful
# for testing in the REPL.
PrimeSieveStripedBlocks(sieve_size::Int) = PrimeSieveStripedBlocks(UInt(sieve_size))


@inline function PrimesSolution3.unsafe_find_next_factor_index(
    arr::Vector{<:Unsigned},
    start_index::Integer,
    max_index::Integer
)
    # This loop calculates indices as if they are zero-based then adds
    # 1 when accessing the array since Julia uses 1-based indexing.
    zero_index = start_index
    @inbounds while zero_index < max_index
        if iszero(
            arr[_div_uint_size(zero_index) + 1] & (MainUInt(1) << _mod_uint_size(zero_index))
        )
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
    block_idx_start = start ÷ BLOCK_SIZE_BITS
    offset_idx = start % BLOCK_SIZE_BITS
    bit_idx = offset_idx ÷ BLOCK_SIZE
    word_idx = offset_idx % BLOCK_SIZE

    @inbounds while block_idx < num_blocks
        block = blocks[block_idx + 1]
        while bit_idx < UINT_BIT_LENGTH
            # Calculate length of current stripe, if it is less than
            # BLOCK_SIZE, then we know that this should be the last
            # iteration.
            stripe_start_position = block_idx * BLOCK_SIZE_BITS + bit_idx * BLOCK_SIZE
            effective_len = min(BLOCK_SIZE, sieve.length_bits - stripe_start_position)
            mask = !(1 << bit_idx)
            # TODO: Check if loop unrolling helps here.
            while word_idx < effective_len
                block[word_idx + 1] &= mask
                word_idx += skip
            end
            # Last iteration
            if effective_len != BLOCK_SIZE
                return
            end
            bit_idx += 1
            word_idx -= BLOCK_SIZE
        end
        bit_idx = 0
        block_idx += 1
    end
end

function PrimesSolution3.run_sieve!(sieve::PrimeSieveStripedBlocks)
    is_not_prime = sieve.is_not_prime
    sieve_size = sieve.sieve_size
    max_bits_index = _map_to_index(sieve_size)
    max_factor_index = _map_to_index(unsafe_trunc(UInt, sqrt(sieve_size)))
    factor_index = UInt(1) # 1 => 3, 2 => 5, 3 => 7, ...
    while factor_index <= max_factor_index
        PrimesSolution3.unsafe_clear_factors!(is_not_prime, factor_index, max_bits_index)
        factor_index = PrimesSolution3.unsafe_find_next_factor_index(
            is_not_prime, factor_index, max_factor_index
        )
    end
    return is_not_prime
end


# These functions aren't optimized, but they aren't being benchmarked,
# so it's fine.

@inline function unsafe_get_bit_at_index(arr::Vector{<:Unsigned}, index::Integer)
    zero_index = index - 1
    return @inbounds arr[_div_uint_size(zero_index) + 1] & (MainUInt(1) << _mod_uint_size(zero_index))
end

function PrimesSolution3.count_primes(sieve::PrimeSieveStripedBlocks)
    arr = sieve.is_not_prime
    max_bits_index = _map_to_index(sieve.sieve_size)
    # Since we start clearing factors at 3, we include 2 in the count
    # beforehand.
    count = 1
    for i in 1:max_bits_index
        if iszero(unsafe_get_bit_at_index(arr, i))
            count += 1
        end
    end
    return count
end

function PrimesSolution3.get_found_primes(sieve::PrimeSieveStripedBlocks)
    arr = sieve.is_not_prime
    sieve_size = sieve.sieve_size
    max_bits_index = _map_to_index(sieve_size)
    output = [2]
    # Int(sieve_size) may overflow if sieve_size is too large (most
    # likely only a problem for 32-bit systems)
    for (index, number) in zip(1:max_bits_index, 3:2:Int(sieve_size))
        if iszero(unsafe_get_bit_at_index(arr, index))
            push!(output, number)
        end
    end
    return output
end

end
