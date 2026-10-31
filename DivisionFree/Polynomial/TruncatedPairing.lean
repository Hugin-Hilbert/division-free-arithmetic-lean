import DivisionFree.Polynomial.CoefficientPairing
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The truncated polynomial product is self-adjoint under the reversed pairing. -/

namespace DivisionFree
namespace PolynomialArithmetic

open scoped BigOperators

noncomputable def mulVector {R : Type*} [CommRing R] {q : ℕ}
    (a b : Fin q → R) : Fin q → R :=
  fun t => (vectorPolynomial q a * vectorPolynomial q b).coeff t.val

private theorem coeff_mul_eq_of_coeff_eq {R : Type*} [CommRing R]
    (q d : ℕ) (hd : d < q) (p p' b : Polynomial R)
    (hp : ∀ i < q, p.coeff i = p'.coeff i) :
    (p * b).coeff d = (p' * b).coeff d := by
  classical
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < q := lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) hd
  rw [hp i.val hi]

theorem mulVector_pairing {R : Type*} [CommRing R] {q : ℕ}
    (hq : 0 < q) (a x y : Fin q → R) :
    mulVector a x ⬝ᵥ reverse y = x ⬝ᵥ reverse (mulVector a y) := by
  classical
  let P : (Fin q → R) → Polynomial R := vectorPolynomial q
  have hleftLow : ∀ i < q,
      (P (mulVector a x)).coeff i = (P a * P x).coeff i := by
    intro i hi
    simp [P, mulVector, vectorPolynomial_coeff_of_lt q i (mulVector a x) hi]
  have hrightLow : ∀ i < q,
      (P (mulVector a y)).coeff i = (P a * P y).coeff i := by
    intro i hi
    simp [P, mulVector, vectorPolynomial_coeff_of_lt q i (mulVector a y) hi]
  have hleft := coeff_mul_eq_of_coeff_eq q (q - 1) (by omega)
    (P (mulVector a x)) (P a * P x) (P y) hleftLow
  have hright := coeff_mul_eq_of_coeff_eq q (q - 1) (by omega)
    (P (mulVector a y)) (P a * P y) (P x) hrightLow
  have hpairLeft :
      mulVector a x ⬝ᵥ reverse y =
        ((P (mulVector a x)) * P y).coeff (q - 1) := by
    change (∑ i : Fin q, mulVector a x i * y i.rev) = _
    rw [← vectorPolynomial_mul_coeff_last q hq (mulVector a x) y]
  have hpairRight :
      x ⬝ᵥ reverse (mulVector a y) =
        ((P x) * P (mulVector a y)).coeff (q - 1) := by
    change (∑ i : Fin q, x i * mulVector a y i.rev) = _
    rw [← vectorPolynomial_mul_coeff_last q hq x (mulVector a y)]
  calc
    mulVector a x ⬝ᵥ reverse y =
        ((P (mulVector a x)) * P y).coeff (q - 1) := hpairLeft
    _ = ((P a * P x) * P y).coeff (q - 1) := hleft
    _ = ((P a * P y) * P x).coeff (q - 1) := by ring_nf
    _ = (P (mulVector a y) * P x).coeff (q - 1) := hright.symm
    _ = ((P x) * P (mulVector a y)).coeff (q - 1) := by rw [mul_comm]
    _ = x ⬝ᵥ reverse (mulVector a y) := hpairRight.symm

end PolynomialArithmetic
end DivisionFree
