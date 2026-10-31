# Arithmetic interfaces and resource model

This document specifies the arithmetic interfaces. The proved declarations and
their scope are listed in [STATUS.md](STATUS.md).

## Coefficient rings and circuits

The final arithmetic interfaces apply to every commutative ring with identity,
including the zero ring and rings with zero divisors. They impose no restriction
on characteristic and require neither roots of unity nor division by integers
in the coefficient ring.

Arithmetic costs count addition, negation, and multiplication gates in the
restricted `Circuit` syntax. Integer constants are charged separately by their
bit lengths. Parameter preparation, transforms, padding, and modulus
preprocessing are included in the complete algorithms. A local transposition
lemma may take fixed scalars as inputs; the algorithm using it accounts for
their preparation.

## Full polynomial multiplication

Two coefficient vectors of length `n` produce the full polynomial product.
The output has `2n` slots, with the final slot zero when `n > 0`. Bounds cover
zero-length inputs and the zero ring.

The required Cantor–Kaltofen bounds are `O(n log n log log n)` additions and
negations and `O(n log n)` multiplications, with constants independent of the
coefficient ring and the input values. A bound on multiplication rank alone,
a truncated product, or a larger subquadratic bound does not specify this
interface.

The bilinear interface has separate left and right linear stages, a layer of
paired products, and an output linear stage. Fixed-factor forward and transpose
programs include shared parameter preparation and carry syntactic cost bounds.

## Series inverse and monic remainder

For a series with constant coefficient one, the inverse interface computes its
first `n` coefficients. Its recursive correctness and resource bounds include
the polynomial multiplications made by Newton iteration.

For a monic polynomial of degree `n`, the remainder interface accepts a full
length-`2n` input and returns the complete remainder. It includes preparation of
the reflected inverse of the modulus. For a fixed modulus, the remainder is
represented by a linear program with forward and transpose resource bounds.
Both algorithms retain `O(n log n log log n)` arithmetic cost.

## Transposition and coefficient extensions

A linear straight-line program of cost `c` with `r` inputs and `s` outputs has
transpose cost `O(c+r+s)`, including repeated outputs, shared values, and zero
outputs. Coefficient-reversal transposition at truncation precision `q` has
base-ring cost `O(c+(r+s)q)`; its hypotheses include the specified forward
coefficient program.

Multivariate Kronecker encoding retains the full product range: width `2s_i-1`
in each coordinate and width `2q-1` in a truncation variable before cropping.
The interface includes the no-alias identity and the softly linear
`O~(2^k Nq)` base-ring cost. Multiplication in a general monic quotient also
accounts for monic reduction.

## Interpretation of resource bounds

Algebraic correctness, circuit gate counts, integer-constant bits, and program
construction time are distinct statements. Some circuit definitions are
`noncomputable` mathematical constructions. Their resource bounds do not imply
a construction-time or evaluation-time theorem. A downstream application does
not change the hypotheses or resource requirements of these interfaces.
