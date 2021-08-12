# Solution based on PrimeRust/solution_1 (FlagStorageBitVectorStripedBlocks)
# by Michael Barber (@mike-barber).

module PrimesStriped
export PrimeSieveStripedBlocks

import ..PrimesSolution3

const BlockUInt = UInt8
const ExtraBitsUInt = UInt32
# If MainUInt is longer than Int, the bit mask calculation in
# clear_stripe (1 << bit_index) won't work.
# For some reason, 1 << bit_index is faster than MainUInt(1) << bit_index.
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
    total_bits = (sieve_size - 1) ÷ 2
    num_blocks = total_bits ÷ BLOCK_SIZE_BITS
    total_blocks_bits = num_blocks * BLOCK_SIZE_BITS
    total_extra_bits = total_bits - total_blocks_bits
    # This is a little compliated.
    # sieve.blocks is a striped bit vector while sieve.extra_bits is an
    # inverted bit vector.
    return PrimeSieveStripedBlocks(
        sieve_size,
        total_bits,
        [fill(typemax(BlockUInt), BLOCK_SIZE) for _ in 1:num_blocks],
        total_blocks_bits,
        zeros(
            ExtraBitsUInt,
            (total_extra_bits + EXTRABITSUINT_BIT_LENGTH - 1) ÷ EXTRABITSUINT_BIT_LENGTH
        ),
        total_extra_bits,
    )
end

# The main() function uses the UInt constructor; this is mostly useful
# for testing in the REPL.
PrimeSieveStripedBlocks(sieve_size::Int) = PrimeSieveStripedBlocks(UInt(sieve_size))

Base.@propagate_inbounds function unsafe_get_bit_at_zero_index(
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
        word = sieve.blocks[block_index + 1][word_index + 1]
        return !iszero(word & (1 << bit_index))
    end
end

@inline unsafe_get_bit_at_index(
    sieve::PrimeSieveStripedBlocks, index::Integer
) = unsafe_get_bit_at_zero_index(sieve, index - 1)

Base.@propagate_inbounds function clear_stripe!(
    block::Vector{BlockUInt},
    word_index::Integer,
    skip::Integer,
    mask::Integer,
)
    skip3 = skip * 3
    skip4 = skip * 4
    if BLOCK_SIZE > skip3
        block_size_minus_skip3 = BLOCK_SIZE - skip3
        while word_index < block_size_minus_skip3
            block[word_index            + 1] &= mask
            block[word_index + skip     + 1] &= mask
            block[word_index + skip * 2 + 1] &= mask
            block[word_index + skip * 3 + 1] &= mask
            word_index += skip4
        end
    end
    while word_index < BLOCK_SIZE
        block[word_index + 1] &= mask
        word_index += skip
    end
    return word_index
end

Base.@propagate_inbounds function clear_blocks!(
    blocks::Vector{Vector{BlockUInt}},
    block_index::Integer,
    bit_index::Integer,
    word_index::Integer,
    skip::Integer
)
    max_block_index = length(blocks)
    while block_index < max_block_index
        block = blocks[block_index + 1]
        while bit_index < BLOCKUINT_BIT_LENGTH
            mask = ~(1 << bit_index)
            word_index = clear_stripe!(block, word_index, skip, mask)
            bit_index += 1
            word_index -= BLOCK_SIZE
        end
        bit_index = zero(bit_index)
        block_index += 1
    end
    return word_index
end

Base.@propagate_inbounds function clear_extra_bits!(
    extra_bits::Vector{ExtraBitsUInt},
    start::Integer,
    skip::Integer,
    stop::Integer
)
    i = start
    while i < stop
        extra_bits[i ÷ EXTRABITSUINT_BIT_LENGTH + 1] |=
            ExtraBitsUInt(1) << (i % EXTRABITSUINT_BIT_LENGTH)
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
        @inbounds clear_extra_bits!(
            sieve.extra_bits, start, skip, sieve.total_extra_bits
        )
        return
    else
        block_index = start ÷ BLOCK_SIZE_BITS
        offset_index = start % BLOCK_SIZE_BITS
        bit_index = offset_index ÷ BLOCK_SIZE
        word_index = offset_index % BLOCK_SIZE
        extra_start_index = @inbounds clear_blocks!(
            sieve.blocks, block_index, bit_index, word_index, skip
        )
        @inbounds clear_extra_bits!(
            sieve.extra_bits, extra_start_index, skip, sieve.total_extra_bits
        )
    end
end

function PrimesSolution3.run_sieve!(sieve::PrimeSieveStripedBlocks)
    max_factor_index = _map_to_index(
        unsafe_trunc(UInt, sqrt(sieve.sieve_size))
    )
    factor_index = UInt(1) # 1 => 3, 2 => 5, 3 => 7, ...
    while factor_index <= max_factor_index
        if unsafe_get_bit_at_zero_index(sieve, factor_index)
            PrimesSolution3.unsafe_clear_factors!(sieve, factor_index)
        end
        factor_index += 1
    end
    return sieve
end


# These functions aren't optimized, but they aren't being benchmarked,
# so it's fine.
function PrimesSolution3.count_primes(sieve::PrimeSieveStripedBlocks)
    # Since we start clearing factors at 3, we include 2 in the count
    # beforehand.
    count = 1
    for i in 2:sieve.total_bits
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
    for (index, number) in zip(2:sieve.total_bits, 3:2:Int(sieve.sieve_size))
        if unsafe_get_bit_at_index(sieve, index)
            push!(output, number)
        end
    end
    return output
end

end
