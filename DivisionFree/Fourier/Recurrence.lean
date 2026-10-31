import Mathlib.Tactic

/-! A generic polynomial bound for a padded radix recursion. -/

namespace DivisionFree.Fourier

private theorem paddedRecurrence_step (t : ℕ) (ht : 1 ≤ t) :
    3 * (t / 2 + 1) ^ 3 + (t + 1) ≤ (t + 1) ^ 3 := by
  have hdiv : t = 2 * (t / 2) + t % 2 := by omega
  have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · rw [hmod] at hdiv
    rw [hdiv]
    have hquot : (2 * (t / 2) + 0) / 2 = t / 2 := by omega
    rw [hquot]
    have hqpos : 1 ≤ t / 2 := by omega
    nlinarith [sq_nonneg (t / 2 : ℕ),
      mul_nonneg (show 0 ≤ (t / 2 : ℕ) - 1 by omega)
        (show 0 ≤ 5 * (t / 2 : ℕ) ^ 2 + 8 * (t / 2 : ℕ) + 3 by positivity)]
  · rw [hmod] at hdiv
    rw [hdiv]
    have hquot : (2 * (t / 2) + 1) / 2 = t / 2 := by omega
    rw [hquot]
    have hq : 0 ≤ (t / 2 : ℕ) := Nat.zero_le _
    nlinarith [sq_nonneg (t / 2 : ℕ),
      mul_nonneg hq (sq_nonneg (t / 2 : ℕ)),
      mul_nonneg hq (sq_nonneg ((t / 2 : ℕ) + 1))]

/-- The recursion `W t ≤ 3 W (t / 2) + K (t + 1)` has a cubic
natural-number upper bound with the same coefficient `K`. -/
theorem recurrence_cubic_bound (W : ℕ → ℕ) (K : ℕ)
    (hzero : W 0 ≤ K)
    (hstep : ∀ t, 0 < t → W t ≤ 3 * W (t / 2) + K * (t + 1)) :
    ∀ t, W t ≤ K * (t + 1) ^ 3 := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t = 0
    · subst t
      simpa using hzero
    · have htpos : 0 < t := Nat.pos_of_ne_zero ht
      have hhalf : t / 2 < t := by omega
      have hrec := hstep t htpos
      have hih := ih (t / 2) hhalf
      calc
        W t ≤ 3 * W (t / 2) + K * (t + 1) := hrec
        _ ≤ 3 * (K * (t / 2 + 1) ^ 3) + K * (t + 1) := by omega
        _ = K * (3 * (t / 2 + 1) ^ 3 + (t + 1)) := by ring
        _ ≤ K * (t + 1) ^ 3 := Nat.mul_le_mul_left K (paddedRecurrence_step t (by omega))

end DivisionFree.Fourier
