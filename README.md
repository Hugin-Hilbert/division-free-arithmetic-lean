# Division-free arithmetic in Lean

English | [简体中文](README.zh-CN.md)

We formalize division-free arithmetic over arbitrary commutative rings with identity, including the zero ring, in Lean. Our library provides restricted arithmetic circuits and proofs of their correctness, operation counts, and linear structure for polynomial multiplication, power series inversion, monic reduction, and linear program transposition.

## Main results

The asymptotic bounds below use the coefficient-vector length `n` as their parameter. The main polynomial arithmetic theorems also handle zero length and the zero ring.

- **Full polynomial multiplication:** `fastFullMultiplier` computes the full product of two coefficient vectors of length `n`. The Cantor–Kaltofen circuit uses `O(n log n log log n)` arithmetic gates, including `O(n log n)` multiplication gates, and has `O(n log n)` total integer-constant bits. The bounds include transform preparation, padding, normalization, and Bézout recombination. See `Polynomial.FastMultiplication`, `Polynomial.CantorMultiplication`, and `Polynomial.CantorFullBounds`.
- **Bilinear and fixed-factor programs:** A bilinear circuit for the full product, with shared preparation, uses `O(n log n log log n)` gates and has multiplication rank `O(n log n)`. The fixed-factor forward and transpose linear programs include parameter preparation and use `O(n log n log log n)` gates. See `Polynomial.CantorBilinear` and `Polynomial.CantorPreparedLinear`.
- **Series inversion and monic reduction:** Normalized power series inversion and full monic remainder have `O(n log n log log n)` arithmetic-gate bounds. The fixed-modulus forward and transpose linear programs for monic reduction include preparation of the reflected inverse. See `Polynomial.SeriesInverse`, `Polynomial.CantorNewtonCost`, `Polynomial.MonicReduction`, and `Polynomial.MonicPreparedLinear`.
- **Transposition and multivariate encoding:** Transposition of rectangular linear programs handles shared intermediate values, repeated outputs, and zero outputs. Coefficient-reversal transposition over truncated quotient rings is also proved for positive precision. The full-range mixed-radix Kronecker product interface retains the entire output range in each dimension. See `LinearStraightLine.Transpose`, `LinearStraightLine.QuotientTranspose`, and `Kronecker.FullProduct`.

Gate counts measure ring additions, negations, and multiplications in the circuit syntax; integer-constant bits are counted separately. Some definitions are `noncomputable` mathematical constructions. The gate bounds are not bounds on circuit-generation time or Lean evaluation time. For the precise scope and limitations, see [STATUS.md](docs/STATUS.md); the technical requirements are in [REQUIREMENTS.md](docs/REQUIREMENTS.md).

## Build and use

The project pins Lean **4.32.0** in `lean-toolchain` and mathlib at `81a5d257c8e410db227a6665ed08f64fea08e997`:

```bash
lake exe cache get
python3 scripts/check.py
```

The check builds every source module, audits the axioms of project declarations, and compiles the usage example. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the audit. A downstream Lake project can import `DivisionFree` or individual modules. The example below, also in [FullMultiplication.lean](examples/FullMultiplication.lean), applies the full multiplication correctness theorem.

## Provenance

We adapted `Circuit.lean` and `Recurrence.lean` from the `matmul` project and extracted `Lifting.lean` from our modular-composition formalization. Source hashes, licenses, and adaptation notes are recorded in [PROVENANCE.json](docs/PROVENANCE.json). The library is distributed under Apache-2.0; see [NOTICE](NOTICE).

## Example

```lean
import DivisionFree.Polynomial.FastMultiplication

open DivisionFree.PolynomialArithmetic

example {R : Type} [CommRing R] (n : ℕ) (x : Bool × Fin n → R) :
    vectorPolynomial (2 * n) ((fastFullMultiplier.{0} n).circuit.eval x) =
      vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i)) := by
  exact fastFullMultiplier_correct n x
```

`false` and `true` select the two input vectors, respectively. The output has
`2 * n` coefficients; when `n > 0`, the final coefficient is zero.
