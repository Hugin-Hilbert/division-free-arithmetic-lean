# Arithmetic theorems and scope

The library proves correctness and syntactic resource bounds over arbitrary
commutative rings with identity, including the zero ring. The interfaces are
described in [REQUIREMENTS.md](REQUIREMENTS.md). Run `python3 scripts/check.py`
to build every module, audit all project declarations, and check the usage
example.

## Principal interfaces

Module names below are relative to `DivisionFree`.

| Modules | Interface |
| --- | --- |
| `Circuit`, `Constants` | Arithmetic syntax, interpretation, composition, gate counts, and integer-constant bits |
| `Polynomial.FastMultiplication`, `CantorMultiplication`, `CantorFullBounds` | Full Cantor–Kaltofen polynomial multiplication, with all padding, transforms, normalization, and Bézout combination included |
| `Circuit.BilinearStages`, `BilinearCircuit`, `Polynomial.CantorBilinear` | Bilinear multiplication with one shared preparation and explicit linear stages |
| `Polynomial.CantorPreparedLinear` | Fixed-factor forward and transpose multiplication programs, including preparation |
| `Polynomial.SeriesInverse`, `CantorNewtonCost`, `CantorNewtonResources` | Normalized power series inverse with gate and constant-bit bounds |
| `Polynomial.MonicReduction`, `MonicRemainder`, `MonicPreparedLinear` | Full monic remainder and fixed-modulus forward and transpose programs, including reflected-inverse preparation |
| `LinearStraightLine.Transpose`, `CoefficientTranspose`, `QuotientTranspose` | Rectangular linear transposition and coefficient-reversal transposition over truncated quotient rings |
| `Kronecker.MixedRadix`, `FullProduct` | Full-range product-box encoding, no-alias identities, and one full-multiplier implementation |
| `Circuit.TruncatedLift`, `TruncatedLiftCorrectness`, `TruncatedLiftResources` | Coefficient lifting of arithmetic circuits to truncated polynomial rings |
| `Precision`, `PrecisionTree`, `PrecisionCost`, `Lifting` | Precision splitting, recursion bounds, and algebraic Hensel correction |

## Explicit arithmetic bounds

For full multiplication, let `L = Nat.log 2 (2*n) + 1` and
`T = Nat.log 2 L + 2`. The published `fastFullMultiplier` has:

- total gates at most `893nLT`;
- multiplication gates at most `390nL`;
- integer-constant bits at most `30nL`.

Its output contains all `2n` coefficients, and the proofs cover `n = 0`.
The bilinear alternative has at most `4872nLT` total gates, `3510nL`
multiplication gates, and rank at most `780nL`, with preparation included.
The fixed-factor forward and transpose constructions have total costs at most
`2046nLT` and `3199nLT + 2n`, respectively.

For normalized series inversion, let `A = Nat.log 2 (n+1) + 3`. The total
cost is at most `7148nA(Nat.log 2 A + 2)`, the multiplication count is at most
`3120nA`, and integer-constant bits are at most `240nA`.

For monic remainder, let `B = Nat.log 2 (2n+2) + 3` and
`U = Nat.log 2 B + 2`. The total cost is at most `8935nBU`, with at most
`3900nB` multiplication gates and `300nB + 2` integer-constant bits.
The fixed-modulus forward and transpose programs, including preparation,
have costs at most `19820nBU` and `30705nBU + n`, respectively.

These give `O(n log n log log n)` total gates and `O(n log n)`
multiplication gates for the principal arithmetic operations. The constants
are bounds derived from circuit syntax, rather than measured running times.

## Representation and scope

Full multiplication, normalized inversion, and monic remainder include their
parameter preparation. Local linear-program transposition assumes the supplied
forward program and its fixed scalars; callers account for preparing those
scalars. The full-range Kronecker interface includes the complete output box,
with capacity at most `2^d N` and cost `2N + M.cost` for its chosen multiplier.

Some definitions use classical choice or `noncomputable` representations.
Gate and constant-bit bounds are circuit resource theorems; they do not give
bounds for circuit generation, bit execution time, or Lean evaluation. The
finite-instance example checks theorem use, not runtime performance.

The axiom audit traverses every declaration belonging to library modules,
including generated auxiliaries. It permits only `propext`, `Classical.choice`,
and `Quot.sound`.
