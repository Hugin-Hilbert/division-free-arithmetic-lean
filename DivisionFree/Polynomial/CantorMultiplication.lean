import DivisionFree.Polynomial.FastMultiplication
import DivisionFree.Polynomial.CantorFullBounds
import DivisionFree.Polynomial.TruncatedMultiplication

/-! Cantor--Kaltofen resource bounds for the actual public multiplier.
Both cyclotomic branches, all padding, normalization and the final integer
combination are included. -/

namespace DivisionFree.PolynomialArithmetic

open Fourier

universe u

/-- The actual full multiplier uses `O(n log n log log n)` arithmetic gates.
The bit-size formulation also covers input lengths zero and one. -/
theorem fastFullMultiplier_cantor_cost_le (n : ℕ) :
    (fastFullMultiplier.{u} n).cost ≤
      893 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.size (Nat.log 2 (2 * n) + 1) + 1) := by
  by_cases hn : 1 ≤ n
  · rw [fastFullMultiplier, dif_pos hn]
    have hmerge := combineScaledFullMultipliers_cost_le
      (primePowerFullMultiplier.{u} 2 n Nat.prime_two hn)
      (ternaryFullMultiplier.{u} n hn)
      (twoThreeBounded_identity
        (primePowerScale (paddedExponent 2 n)) (primePowerScale (paddedExponent 3 n)))
    have h2 := binaryFullMultiplier_cantor_cost_le.{u} n hn
    have h3 := ternaryFullMultiplier_cantor_cost_le.{u} n hn
    have hlog : 0 < Nat.log 2 (2 * n) := Nat.log_pos (by omega) (by omega)
    have hL : 2 ≤ Nat.log 2 (2 * n) + 1 := by omega
    have hsize : 2 ≤ Nat.size (Nat.log 2 (2 * n) + 1) := by
      have h := Nat.size_le_size hL
      exact h
    have hfactor : 6 ≤ (Nat.log 2 (2 * n) + 1) *
        (Nat.size (Nat.log 2 (2 * n) + 1) + 1) := by nlinarith
    have hnscale := Nat.mul_le_mul_left n hfactor
    nlinarith
  · have hn0 : n = 0 := by omega
    rw [fastFullMultiplier, dif_neg hn]
    simpa [hn0] using fullSchoolbook_cost_le n

/-- Multiplication gates, including the explicit integer Bézout scaling,
obey the sharper `O(n log n)` bound. -/
theorem fastFullMultiplier_multiplications_le (n : ℕ) :
    (fastFullMultiplier.{u} n).circuit.multiplications ≤
      390 * n * (Nat.log 2 (2 * n) + 1) := by
  by_cases hn : 1 ≤ n
  · rw [fastFullMultiplier, dif_pos hn, combineScaledFullMultipliers_multiplications]
    have h2 := binaryFullMultiplier_cantor_multiplications_le.{u} n hn
    have h3 := ternaryFullMultiplier_cantor_multiplications_le.{u} n hn
    have hlog : 0 < Nat.log 2 (2 * n) := Nat.log_pos (by omega) (by omega)
    have hnscale : 2 * n ≤ n * (Nat.log 2 (2 * n) + 1) := by nlinarith
    nlinarith
  · have hn0 : n = 0 := by omega
    have hc := fastFullMultiplier_cantor_cost_le.{u} n
    have hm : (fastFullMultiplier.{u} n).circuit.multiplications ≤ (fastFullMultiplier.{u} n).cost := by
      unfold FullMultiplier.cost Circuit.cost
      omega
    simpa [hn0] using hm.trans hc

/-- A version of the bound displaying both logarithms explicitly. -/
theorem fastFullMultiplier_cantor_log_cost_le (n : ℕ) :
    (fastFullMultiplier.{u} n).cost ≤
      893 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  have hsize : Nat.size (Nat.log 2 (2 * n) + 1) ≤
      Nat.log 2 (Nat.log 2 (2 * n) + 1) + 1 :=
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) _)
  exact (fastFullMultiplier_cantor_cost_le.{u} n).trans
    (Nat.mul_le_mul_left _ (by omega))

/-- Addition and negation gates satisfy the Cantor--Kaltofen arithmetic bound. -/
theorem fastFullMultiplier_additions_negations_le (n : ℕ) :
    (fastFullMultiplier.{u} n).circuit.additions + (fastFullMultiplier.{u} n).circuit.negations ≤
      893 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  have hc := fastFullMultiplier_cantor_log_cost_le.{u} n
  have hle : (fastFullMultiplier.{u} n).circuit.additions + (fastFullMultiplier.{u} n).circuit.negations ≤
      (fastFullMultiplier.{u} n).cost := by
    unfold FullMultiplier.cost Circuit.cost
    omega
  exact hle.trans hc

/-- The existing truncated-product interface inherits the same arithmetic bound. -/
theorem fastMultiplier_cantor_cost_le (n : ℕ) :
    (fastMultiplier.{u} n).cost ≤
      893 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.log 2 (Nat.log 2 (2 * n) + 1) + 2) := by
  exact fastFullMultiplier_cantor_log_cost_le.{u} n

end DivisionFree.PolynomialArithmetic
