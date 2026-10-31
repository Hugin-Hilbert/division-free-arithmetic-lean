import DivisionFree.Polynomial.VectorResize
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.Fin.Rev

/-! Wire-only reversals of bounded coefficient vectors. -/

namespace DivisionFree.PolynomialArithmetic

open DivisionFree

/-- Reverse a length-`n` vector. -/
def reverseVector (n : ℕ) : Circuit (Fin n) (Fin n) :=
  .wire Fin.rev

@[simp] theorem reverseVector_eval {R : Type*} [Ring R]
    (n : ℕ) (x : Fin n → R) (i : Fin n) :
    (reverseVector n).eval x i = x (Fin.rev i) := rfl

theorem reverseVector_cost (n : ℕ) : (reverseVector n).cost = 0 := rfl

theorem reverseVector_constantBits (n : ℕ) :
    (reverseVector n).constantBits = 0 := rfl

theorem reverseVector_eval_involutive {R : Type*} [Ring R]
    (n : ℕ) (x : Fin n → R) (i : Fin n) :
    (reverseVector n).eval ((reverseVector n).eval x) i = x i := by
  simp [reverseVector, Fin.rev_rev]

/-- Reversing a bounded vector agrees with polynomial reflection about degree
`n-1`, including the empty vector. -/
theorem vectorPolynomial_reverse {R : Type*} [CommRing R]
    (n : ℕ) (x : Fin n → R) :
    vectorPolynomial n ((reverseVector n).eval x) =
      Polynomial.reflect (n - 1) (vectorPolynomial n x) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [vectorPolynomial, reverseVector]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_reflect]
    by_cases hk : k < n
    · rw [vectorPolynomial_coeff_of_lt n k _ hk]
      rw [reverseVector_eval]
      rw [Polynomial.revAt_le (by omega : k ≤ n - 1)]
      have hr : (Fin.rev (⟨k, hk⟩ : Fin n)).val = n - 1 - k := by
        simp [Fin.rev]
        omega
      rw [vectorPolynomial_coeff_of_lt n (n - 1 - k) x (by omega)]
      congr 1
      exact Fin.ext hr
    · rw [vectorPolynomial_coeff_eq_zero_of_ge n k _ (Nat.le_of_not_gt hk)]
      rw [Polynomial.revAt_eq_self_of_lt (by omega : n - 1 < k)]
      exact (vectorPolynomial_coeff_eq_zero_of_ge n k x (Nat.le_of_not_gt hk)).symm

/-- Reverse the high half of a length-`2*n` vector into a length-`n` vector. -/
def highReverse (n : ℕ) : Circuit (Fin (2 * n)) (Fin n) :=
  .wire fun i => ⟨2 * n - 1 - i.val, by omega⟩

@[simp] theorem highReverse_eval {R : Type*} [Ring R]
    (n : ℕ) (x : Fin (2 * n) → R) (i : Fin n) :
    (highReverse n).eval x i = x ⟨2 * n - 1 - i.val, by omega⟩ := rfl

theorem highReverse_cost (n : ℕ) : (highReverse n).cost = 0 := rfl

theorem highReverse_constantBits (n : ℕ) :
    (highReverse n).constantBits = 0 := rfl

/-- The high-half reversal is the low-degree truncation of the reflection of
the full length-`2*n` coefficient polynomial. -/
theorem vectorPolynomial_highReverse_mod {R : Type*} [CommRing R]
    (n : ℕ) (x : Fin (2 * n) → R) :
    vectorPolynomial n ((highReverse n).eval x) =
      Polynomial.reflect (2 * n - 1) (vectorPolynomial (2 * n) x) %ₘ
        (Polynomial.X ^ n) := by
  classical
  apply Polynomial.ext
  intro k
  rw [modByMonic_X_pow_coeff]
  by_cases hk : k < n
  · rw [if_pos hk]
    rw [vectorPolynomial_coeff_of_lt n k _ hk, highReverse_eval,
      Polynomial.coeff_reflect, Polynomial.revAt_le (by omega : k ≤ 2 * n - 1)]
    have hidx : 2 * n - 1 - k < 2 * n := by omega
    rw [vectorPolynomial_coeff_of_lt (2 * n) (2 * n - 1 - k) x hidx]
  · rw [if_neg hk]
    exact vectorPolynomial_coeff_eq_zero_of_ge n k _ (Nat.le_of_not_gt hk)

end DivisionFree.PolynomialArithmetic
