import DivisionFree.Recurrence

/-! Precision splitting and the critical dyadic recurrence, with constants
kept explicit so that other algorithm parameters may vary. -/

namespace DivisionFree.Precision

open scoped BigOperators

theorem split_sum (q : ℕ) : q / 2 + (q - q / 2) = q :=
  Nat.add_sub_of_le (Nat.div_le_self q 2)

theorem split_bounds (q : ℕ) (hq : 2 ≤ q) :
    0 < q / 2 ∧ q / 2 < q ∧ 0 < q - q / 2 ∧ q - q / 2 < q := by
  omega

theorem split_balanced (q : ℕ) : q - q / 2 ≤ q / 2 + 1 := by omega

/-- If a node's two precision children sum to its precision, a linear
precision budget is preserved across that level. -/
theorem split_linear_budget (K q : ℕ) :
    K * (q / 2) + K * (q - q / 2) = K * q := by
  rw [← Nat.mul_add, split_sum]

theorem dyadic_recurrence (C : ℕ → ℕ) (base K : ℕ)
    (hzero : C 0 ≤ base)
    (hstep : ∀ k, C (k + 1) ≤ 2 * C k + K * 2 ^ k) (k : ℕ) :
    C k ≤ (base + K * k) * 2 ^ k :=
  Recurrence.recurrence_bound C base K 2 2 (by decide) (by decide) hzero hstep k

/-- The same critical recurrence with a level-dependent normalized toll.
This keeps logarithmic factors and all external parameters explicit. -/
theorem dyadic_level_sum (C toll : ℕ → ℕ) (base : ℕ)
    (hzero : C 0 ≤ base)
    (hstep : ∀ k, C (k + 1) ≤ 2 * C k + 2 ^ (k + 1) * toll k) (k : ℕ) :
    C k ≤ 2 ^ k * (base + ∑ i ∈ Finset.range k, toll i) := by
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    calc
      C (k + 1) ≤ 2 * C k + 2 ^ (k + 1) * toll k := hstep k
      _ ≤ 2 * (2 ^ k * (base + ∑ i ∈ Finset.range k, toll i)) +
          2 ^ (k + 1) * toll k := Nat.add_le_add_right (Nat.mul_le_mul_left 2 ih) _
      _ = 2 ^ (k + 1) * (base + ∑ i ∈ Finset.range (k + 1), toll i) := by
        rw [Finset.sum_range_succ, pow_succ]
        ring

end DivisionFree.Precision
