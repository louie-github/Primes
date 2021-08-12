using PrimesSolution3

for PrimeSieveImplementation in PrimesSolution3.IMPLEMENTATIONS
    println(stderr,
        "Precompiling ",
        string(nameof(PrimeSieveImplementation)),
        "..."
    )
    run_sieve!(PrimeSieveImplementation(UInt(1_000_000)))
end
