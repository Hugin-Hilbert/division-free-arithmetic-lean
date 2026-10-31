import DivisionFree.Polynomial.CoefficientMatrix
import DivisionFree.Polynomial.TruncatedQuotient

/-! Relate coefficient-matrix semantics to matrices in the actual quotient
ring `R[t]/(t^q)`. No nontriviality or characteristic hypothesis is needed. -/

namespace DivisionFree.PolynomialArithmetic

open Matrix
open scoped BigOperators

variable {r s q : ℕ} {R : Type*} [CommRing R]

/-- The unique bounded coefficient vector. This is a mathematical decoding
specification; circuits already take the coefficients as their inputs. -/
noncomputable def coefficients (z : TruncatedRing R q) : Fin q → R :=
  Classical.choose (toTruncated_surjective q z)

@[simp] theorem toTruncated_coefficients (z : TruncatedRing R q) :
    toTruncated (coefficients z) = z :=
  Classical.choose_spec (toTruncated_surjective q z)

@[simp] theorem coefficients_toTruncated (x : Fin q → R) :
    coefficients (toTruncated x) = x := by
  apply toTruncated_injective q
  exact toTruncated_coefficients _

noncomputable def toBlocks (x : Fin r → Fin q → R) : Fin r → TruncatedRing R q :=
  fun i => toTruncated (x i)

@[simp] theorem toBlocks_coefficients (b : Fin r → TruncatedRing R q) :
    toBlocks (fun i => coefficients (b i)) = b := by
  funext i
  exact toTruncated_coefficients _

noncomputable def matrixCoefficients (A : Matrix (Fin r) (Fin s) (TruncatedRing R q)) :
    Fin r → Fin s → Fin q → R := fun i j => coefficients (A i j)

@[simp] theorem matrixCoefficients_transpose
    (A : Matrix (Fin r) (Fin s) (TruncatedRing R q)) :
    matrixCoefficients A.transpose = blockTranspose (matrixCoefficients A) := rfl

theorem toBlocks_blockMul (A : Matrix (Fin r) (Fin s) (TruncatedRing R q))
    (x : Fin s → Fin q → R) :
    toBlocks (blockMul (matrixCoefficients A) x) = A *ᵥ toBlocks x := by
  funext i
  simp [toBlocks, blockMul, matrixCoefficients, toTruncated_sum,
    toTruncated_mulVector, Matrix.mulVec, dotProduct]

theorem coefficientMap_quotient (A : Matrix (Fin r) (Fin s) (TruncatedRing R q))
    (x : Fin (s * q) → R) :
    toBlocks (unflatten (coefficientMap (matrixCoefficients A) x)) =
      A *ᵥ toBlocks (unflatten x) := by
  simpa only [coefficientMap, unflatten_flatten] using toBlocks_blockMul A (unflatten x)

end DivisionFree.PolynomialArithmetic
