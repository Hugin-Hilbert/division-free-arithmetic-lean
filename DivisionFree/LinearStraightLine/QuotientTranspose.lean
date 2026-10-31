import DivisionFree.LinearStraightLine.CoefficientTranspose
import DivisionFree.Polynomial.QuotientMatrix

/-! The base-ring transposed circuit computes the transpose of a matrix over
the actual truncated quotient ring, using the same scalar parameters. -/

namespace DivisionFree.LinearStraightLine

open PolynomialArithmetic Matrix

variable {r s q k : ℕ} {R : Type*} [CommRing R]

theorem Program.transposeQuotient_correct (hq : 0 < q)
    (P : Program k (s * q) (r * q)) (p : Fin k → R)
    (A : Matrix (Fin r) (Fin s) (TruncatedRing R q))
    (hP : ∀ x, P.eval p x = coefficientMap (matrixCoefficients A) x)
    (b : Fin r → TruncatedRing R q) :
    toBlocks (unflatten (P.transposeCoefficients.eval
      (Sum.elim p (flatten (fun i => coefficients (b i)))))) = A.transpose *ᵥ b := by
  rw [P.transposeCoefficients_correct hq p (matrixCoefficients A) hP]
  rw [← matrixCoefficients_transpose, coefficientMap_quotient]
  simp

end DivisionFree.LinearStraightLine
