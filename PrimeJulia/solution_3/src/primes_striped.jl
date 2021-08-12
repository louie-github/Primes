# Solution based on PrimeRust/solution_1 (FlagStorageBitVectorStripedBlocks)
# by Michael Barber (@mike-barber).

module PrimesStriped
export PrimeSieveStripedBlocks

import ..PrimesSolution3

const BlockUInt = UInt8
const ExtraBitsUInt = UInt32
# If MainUInt is longer than Int, the bit mask calculation in
# clear_stripe (1 << bit_idx) won't work.
# For some reason, 1 << bit_idx is faster than MainUInt(1) << bit_idx.
if sizeof(BlockUInt) > sizeof(Int)
    error("BlockUInt must not be larger than native UInt type.")
end
const BLOCKUINT_BIT_LENGTH = sizeof(BlockUInt) * 8
const EXTRABITSUINT_BIT_LENGTH = sizeof(ExtraBitsUInt) * 8 
const BLOCK_SIZE = 16 * 1024
const BLOCK_SIZE_BITS = BLOCK_SIZE * BLOCKUINT_BIT_LENGTH

@inline _mul2(i::Integer) = i << 1
@inline _div2(i::Integer) = i >> 1
@inline _map_to_index(i::Integer) = _div2(i - 1)
@inline _map_to_factor(i::Integer) = _mul2(i) + 1

struct PrimeSieveStripedBlocks <: PrimesSolution3.AbstractPrimeSieve
    sieve_size::UInt
    total_bits::UInt
    blocks::Vector{Vector{BlockUInt}}
    total_blocks_bits::UInt
    extra_bits::Vector{ExtraBitsUInt}
    total_extra_bits::UInt
end


function PrimeSieveStripedBlocks(sieve_size::UInt)
    sieve_size ÷= 2
    num_blocks = sieve_size ÷ BLOCK_SIZE_BITS
    total_bits_in_blocks = sieve_size * BLOCK_SIZE_BITS
    num_extra_bits = sieve_size % BLOCK_SIZE_BITS
    return PrimeSieveStripedBlocks(
        sieve_size,
        _map_to_index(sieve_size),
        [fill(typemax(BlockUInt), BLOCK_SIZE) for _ in 1:num_blocks],
        total_bits_in_blocks,
        zeros(
            ExtraBitsUInt,
            (num_extra_bits + EXTRABITSUINT_BIT_LENGTH - 1) ÷ EXTRABITSUINT_BIT_LENGTH
        ),
        num_extra_bits
    )
end

# The main() function uses the UInt constructor; this is mostly useful
# for testing in the REPL.
PrimeSieveStripedBlocks(sieve_size::Int) = PrimeSieveStripedBlocks(UInt(sieve_size))

@inline function unsafe_get_bit_at_zero_index(
    sieve::PrimeSieveStripedBlocks, index::Integer
)
    if index >= sieve.total_bits
        return false
    elseif index >= sieve.total_blocks_bits
        index -= sieve.total_blocks_bits
        return iszero(
            sieve.extra_bits[index ÷ EXTRABITSUINT_BIT_LENGTH + 1] & 
            (1 << (index % EXTRABITSUINT_BIT_LENGTH))
        )
    else
        block_index = index ÷ BLOCK_SIZE_BITS
        offset = index % BLOCK_SIZE_BITS
        bit_index = offset ÷ BLOCK_SIZE
        word_index = offset % BLOCK_SIZE
        word = @inbounds sieve.blocks[block_index + 1][word_index + 1]
        return !iszero(word & (1 << bit_index))
    end
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
    # This could be made faster by emulating the striped access instead
    # of calculating the index each time via unsafe_get_bit_at_zero_index.
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

Base.@propagate_inbounds function clear_stripe!(
    block::Vector{BlockUInt},
    word_idx::Integer,
    skip::Integer,
    mask::Integer,
    end_index::Integer
)
    skip3 = skip * 3
    skip4 = skip * 4
    if end_index > skip3
        end_index_minus_skip3 = end_index - skip3
        while word_idx < end_index_minus_skip3
            block[word_idx            + 1] &= mask
            block[word_idx + skip     + 1] &= mask
            block[word_idx + skip * 2 + 1] &= mask
            block[word_idx + skip * 3 + 1] &= mask
            word_idx += skip4
        end
    end
    while word_idx < end_index
        block[word_idx + 1] &= mask
        word_idx += skip
    end
    return word_idx
end

Base.@propagate_inbounds function clear_extra_bits!(
    sieve::PrimeSieveStripedBlocks,
    start::Integer,
    skip::Integer,
)
    i = start
    while i < sieve.total_extra_bits
        sieve.extra_bits[i ÷ EXTRABITSUINT_BIT_LENGTH + 1] |= 1 << (i % EXTRABITSUINT_BIT_LENGTH)
        i += skip
    end
end

function PrimesSolution3.unsafe_clear_factors!(
    sieve::PrimeSieveStripedBlocks,
    factor_index::Integer
)
    factor = _map_to_factor(factor_index)
    start = factor * factor ÷ 2
    skip = factor
    if start >= sieve.total_blocks_bits
        start -= sieve.total_blocks_bits
        @inbounds clear_extra_bits!(sieve, start, skip)
        return
    end

    blocks = sieve.blocks
    num_blocks = length(blocks)
    length_bits = sieve.total_bits

    block_index = start ÷ BLOCK_SIZE_BITS
    offset_index = start % BLOCK_SIZE_BITS
    bit_index = offset_index ÷ BLOCK_SIZE
    word_index = offset_index % BLOCK_SIZE

    @inbounds while block_index < num_blocks
        block = blocks[block_index + 1]
        while bit_index < BLOCKUINT_BIT_LENGTH
            mask = ~(1 << bit_index)
            word_index = clear_stripe!(block, word_index, skip, mask, BLOCK_SIZE)
            bit_index += 1
            word_index -= BLOCK_SIZE
        end
        # Using zero function here so that bit_idx is type stable.
        bit_index = zero(bit_index)
        block_index += 1
    end
    
    index = block_index * BLOCK_SIZE_BITS + bit_index * BLOCK_SIZE + word_index
    index -= sieve.total_blocks_bits
    clear_extra_bits!(sieve, index, skip)
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
    for i in 1:sieve.total_bits
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
    for (index, number) in zip(1:sieve.total_bits, 3:2:Int(sieve.sieve_size))
        if unsafe_get_bit_at_index(sieve, index)
            push!(output, number)
        end
    end
    return output
end

end
