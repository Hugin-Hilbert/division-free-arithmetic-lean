import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Constant-bit envelopes for the Newton circuit recurrence and dyadic
padding. These are estimates conditional on the displayed recurrence
hypotheses, not algorithm claims. -/

namespace DivisionFree.PolynomialArithmetic

/-- The stated Newton constant-bit recurrence implies a linear-level envelope. -/
theorem newtonBits_recurrence_bound (B : ℕ → ℕ)
    (hzero : B 0 ≤ 2)
    (hstep : ∀ k, B (k + 1) ≤ B k + 60 * 2 ^ (k + 1) * (k + 3) + 3) :
    ∀ k, B k ≤ 120 * 2 ^ k * (k + 2) := by
  intro k
  induction k with
  | zero => exact hzero.trans (by norm_num)
  | succ k ih =>
      have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      have hrec := hstep k
      rw [pow_succ] at hrec
      calc
        B (k + 1) ≤ B k + 60 * (2 ^ k * 2) * (k + 3) + 3 := hrec
        _ ≤ 120 * 2 ^ k * (k + 2) + 60 * (2 ^ k * 2) * (k + 3) + 3 :=
          Nat.add_le_add_right (Nat.add_le_add_right ih _) 3
        _ ≤ 120 * 2 ^ (k + 1) * (k + 3) := by
          rw [pow_succ]
          nlinarith [hp]

/-- The next dyadic power bounds a positive length within a factor two. -/
theorem dyadicPadding_bounds {n : ℕ} (hn : 1 ≤ n) :
    n ≤ 2 ^ Nat.clog 2 n ∧ 2 ^ Nat.clog 2 n ≤ 2 * n := by
  have hbase : 1 < 2 := by omega
  have hlow : n ≤ 2 ^ Nat.clog 2 n :=
    (Nat.clog_le_iff_le_pow hbase).mp le_rfl
  have hhigh : 2 ^ Nat.clog 2 n ≤ 2 * n := by
    by_cases hk : Nat.clog 2 n = 0
    · have hn1 : n = 1 := by
        have := (Nat.clog_le_iff_le_pow hbase).mp (by simp [hk] : Nat.clog 2 n ≤ 0)
        omega
      simp [hn1]
    · have hkpos : 0 < Nat.clog 2 n := Nat.pos_of_ne_zero hk
      have hprev : Nat.clog 2 n - 1 < Nat.clog 2 n := by omega
      have hlt : 2 ^ (Nat.clog 2 n - 1) < n :=
        (Nat.lt_clog_iff_pow_lt hbase).mp hprev
      have heq : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
      rw [heq, pow_succ]
      nlinarith
  exact ⟨hlow, hhigh⟩

/-- Logarithmic bound for the number of dyadic padding levels. -/
theorem dyadicPadding_levels_bound {n : ℕ} (_hn : 1 ≤ n) :
    Nat.clog 2 n ≤ Nat.log 2 (n + 1) + 1 := by
  apply (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).2
  have hpow := (Nat.lt_pow_succ_log_self (by omega : 1 < 2) (n + 1)).le
  omega

/-- Constant-bit envelope after padding to the next power of two. -/
theorem newtonBits_dyadic_bound (B : ℕ → ℕ)
    (hzero : B 0 ≤ 2)
    (hstep : ∀ k, B (k + 1) ≤ B k + 60 * 2 ^ (k + 1) * (k + 3) + 3)
    {n : ℕ} (hn : 1 ≤ n) :
    B (Nat.clog 2 n) ≤ 240 * n * (Nat.log 2 (n + 1) + 3) := by
  have hB := newtonBits_recurrence_bound B hzero hstep (Nat.clog 2 n)
  have hpad := (dyadicPadding_bounds hn).2
  have hlev := dyadicPadding_levels_bound hn
  have hprod : 2 ^ Nat.clog 2 n * (Nat.clog 2 n + 2) ≤
      (2 * n) * (Nat.log 2 (n + 1) + 3) := by
    exact Nat.mul_le_mul hpad (by omega)
  calc
    B (Nat.clog 2 n) ≤ 120 * 2 ^ Nat.clog 2 n * (Nat.clog 2 n + 2) := hB
    _ ≤ 120 * ((2 * n) * (Nat.log 2 (n + 1) + 3)) :=
      by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 120 hprod
    _ = 240 * n * (Nat.log 2 (n + 1) + 3) := by ring

end DivisionFree.PolynomialArithmetic
