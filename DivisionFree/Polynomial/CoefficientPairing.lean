import DivisionFree.Polynomial.Encoding
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Coefficient pairing identities for the bounded polynomial encoding. -/

namespace DivisionFree
namespace PolynomialArithmetic

open scoped BigOperators

def reverse {R : Type*} {n : ℕ} (x : Fin n → R) : Fin n → R :=
  fun i => x i.rev

theorem reverse_involutive {R : Type*} {n : ℕ} (x : Fin n → R) :
    reverse (reverse x) = x := by
  funext i
  simp [reverse]


theorem vectorPolynomial_mul_coeff_last_succ {R : Type*} [CommRing R]
    (m : ℕ) (a b : Fin (m + 1) → R) :
    (vectorPolynomial (m + 1) a * vectorPolynomial (m + 1) b).coeff m =
      ∑ i : Fin (m + 1), a i * b i.rev := by
  classical
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < m + 1 := i.isLt
  have hrev : i.rev.val < m + 1 := i.rev.isLt
  have hval : i.rev.val = m - i.val := by
    simp only [Fin.rev]
    omega
  have hrevFin : (⟨m - i.val, by omega⟩ : Fin (m + 1)) = i.rev := by
    apply Fin.ext
    exact hval.symm
  rw [vectorPolynomial_coeff_of_lt (m + 1) i.val a hi,
    vectorPolynomial_coeff_of_lt (m + 1) (m - i.val) b (by omega)]
  have hiFin : (⟨i.val, hi⟩ : Fin (m + 1)) = i := Fin.ext rfl
  rw [hiFin, hrevFin]

theorem vectorPolynomial_mul_coeff_last {R : Type*} [CommRing R]
    (n : ℕ) (hn : 0 < n) (a b : Fin n → R) :
    (vectorPolynomial n a * vectorPolynomial n b).coeff (n - 1) =
      ∑ i : Fin n, a i * b i.rev := by
  cases n with
  | zero => omega
  | succ m =>
      simpa using vectorPolynomial_mul_coeff_last_succ m a b

end PolynomialArithmetic
end DivisionFree
