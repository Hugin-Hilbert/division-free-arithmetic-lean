import Mathlib.Tactic

/-! Integer parameters for the recursive split used by fast multiplication.
These lemmas describe exponent arithmetic only; they assert no algorithm or
cost bound. -/

namespace DivisionFree.Fourier

/-- Inner exponent in the recursive split. -/
def innerExponent (Q : ℕ) : ℕ := Q / 2 + 1

/-- Outer exponent in the recursive split. -/
def outerExponent (Q : ℕ) : ℕ := Q - innerExponent Q

theorem innerExponent_lt (Q : ℕ) (hQ : 2 < Q) : innerExponent Q < Q := by
  unfold innerExponent
  omega

theorem two_le_innerExponent (Q : ℕ) (hQ : 2 < Q) : 2 ≤ innerExponent Q := by
  unfold innerExponent
  omega

theorem one_le_outerExponent (Q : ℕ) (hQ : 2 < Q) : 1 ≤ outerExponent Q := by
  unfold outerExponent innerExponent
  omega

theorem exponents_sum (Q : ℕ) (hQ : 2 < Q) : innerExponent Q + outerExponent Q = Q := by
  simp only [outerExponent, innerExponent]
  omega

theorem outer_succ_le_inner (Q : ℕ) : outerExponent Q + 1 ≤ innerExponent Q := by
  have hmod : Q % 2 < 2 := Nat.mod_lt Q (by omega)
  have hdecomp : Q % 2 + Q / 2 * 2 = Q := by simpa [Nat.mul_comm] using (Nat.mod_add_div Q 2)
  simp only [outerExponent, innerExponent]
  omega

theorem inner_sub_two (Q : ℕ) (hQ : 2 < Q) :
    innerExponent Q - 2 = (Q - 2) / 2 := by
  unfold innerExponent
  omega

theorem twice_pow_le_pow_succ {p r : ℕ} (hp : 2 ≤ p) :
    2 * p ^ r ≤ p ^ (r + 1) := by
  rw [pow_succ]
  have hpow : 1 ≤ p ^ r := Nat.one_le_pow r p (by omega)
  nlinarith

theorem pow_succ_dvd_pow {p Q : ℕ} ( _hQ : 2 < Q) :
    p ^ (outerExponent Q + 1) ∣ p ^ innerExponent Q := by
  apply Nat.pow_dvd_pow
  exact outer_succ_le_inner Q

theorem split_powers_mul (p Q : ℕ) (hQ : 2 < Q) :
    p ^ innerExponent Q * p ^ outerExponent Q = p ^ Q := by
  rw [← pow_add, exponents_sum Q hQ]

end DivisionFree.Fourier
