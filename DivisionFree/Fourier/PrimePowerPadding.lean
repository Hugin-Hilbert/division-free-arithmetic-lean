import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Elementary size bounds for the prime-power padding parameters. -/

namespace DivisionFree.Fourier

/-- Exponent giving enough prime-power capacity for `2*n` coefficients. -/
def paddedExponent (p n : ℕ) : ℕ := Nat.log p (2 * n) + 2

theorem paddedExponent_ge_two (p n : ℕ) : 2 ≤ paddedExponent p n := by
  simp [paddedExponent]

theorem paddedExponent_capacity {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) :
    2 * n ≤ (p - 1) * p ^ (paddedExponent p n - 1) := by
  have hp' : 1 < p := by omega
  have hn' : 2 * n ≠ 0 := by omega
  have hlog := Nat.lt_pow_of_log_lt hp' (Nat.lt_succ_self (Nat.log p (2 * n)))
  have hexp : paddedExponent p n - 1 = Nat.log p (2 * n) + 1 := by
    simp [paddedExponent]
  rw [hexp]
  have hfactor : 1 ≤ p - 1 := by omega
  have hmul : p ^ (Nat.log p (2 * n) + 1) ≤
      (p - 1) * p ^ (Nat.log p (2 * n) + 1) := by
    simpa [Nat.mul_comm] using
      (Nat.le_mul_of_pos_right (p ^ (Nat.log p (2 * n) + 1)) (by omega))
  exact le_trans (Nat.le_of_lt hlog) hmul

theorem paddedExponent_total_length {p n : ℕ} (_hp : 2 ≤ p) (hn : 1 ≤ n) :
    p ^ paddedExponent p n ≤ 2 * p ^ 2 * n := by
  have hn' : 2 * n ≠ 0 := by omega
  have hlog := Nat.pow_log_le_self p hn'
  calc
    p ^ paddedExponent p n = p ^ 2 * p ^ Nat.log p (2 * n) := by
      simp [paddedExponent, pow_add, Nat.add_comm]
    _ ≤ p ^ 2 * (2 * n) := Nat.mul_le_mul_left _ hlog
    _ = 2 * p ^ 2 * n := by ring

theorem paddedExponent_total_length_small {p n : ℕ}
    (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3) (hn : 1 ≤ n) :
    p ^ paddedExponent p n ≤ 18 * n := by
  have h := paddedExponent_total_length hp₂ hn
  have hpSq : p ^ 2 ≤ 9 := by nlinarith
  calc
    p ^ paddedExponent p n ≤ 2 * p ^ 2 * n := h
    _ ≤ 18 * n := by nlinarith

/-- The padding exponent, with a nonzero lower bound, is logarithmic in the
input length uniformly for prime bases at least two. -/
theorem paddedExponent_logBound {p n : ℕ} (hp : 2 ≤ p) (_hn : 1 ≤ n) :
    max 1 (paddedExponent p n - 1) ≤ Nat.log 2 (2 * n) + 1 := by
  have hlog : Nat.log p (2 * n) ≤ Nat.log 2 (2 * n) :=
    Nat.log_mono (by omega) (by omega) le_rfl
  simp only [paddedExponent]
  omega

end DivisionFree.Fourier
