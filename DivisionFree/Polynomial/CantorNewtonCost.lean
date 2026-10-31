import DivisionFree.Polynomial.CantorMultiplication
import DivisionFree.Polynomial.MonicReduction
import DivisionFree.Polynomial.NewtonCost
import DivisionFree.Polynomial.NewtonInverse
import DivisionFree.Polynomial.SeriesInverse
import Mathlib.Tactic

/-! Sharp Cantor--Kaltofen cost bounds propagated through the actual Newton
inverse and prepared monic-remainder circuits. -/

namespace DivisionFree.PolynomialArithmetic

universe u

private def newtonCantorWeight (k : ℕ) : ℕ :=
  (k + 2) * (Nat.log 2 (k + 2) + 2)

private theorem newtonCantorWeight_mono (k : ℕ) :
    newtonCantorWeight k ≤ newtonCantorWeight (k + 1) := by
  unfold newtonCantorWeight
  have hlog := Nat.log_mono_right (b := 2) (show k + 2 ≤ k + 3 by omega)
  exact Nat.mul_le_mul (by omega) (Nat.add_le_add_right hlog 2)

private theorem inversePowerCircuit_cantor_step_le (k : ℕ) :
    (inversePowerCircuit.{u} (k + 1)).cost ≤
      (inversePowerCircuit.{u} k).cost +
        1787 * 2 ^ (k + 1) * (k + 3) * (Nat.log 2 (k + 3) + 2) := by
  rw [inversePowerCircuit_step_cost]
  have hm := fastMultiplier_cantor_cost_le (2 ^ (k + 1))
  have hlog : Nat.log 2 (2 * 2 ^ (k + 1)) = k + 2 := by
    rw [← pow_succ', Nat.log_pow (by decide)]
  rw [hlog] at hm
  have hs := twoMinus_cost_le (2 ^ (k + 1))
  have hweight : 2 ≤ (k + 3) * (Nat.log 2 (k + 3) + 2) := by
    have h := Nat.mul_le_mul (show 1 ≤ k + 3 by omega)
      (show 2 ≤ Nat.log 2 (k + 3) + 2 by omega)
    simpa using h
  nlinarith

private theorem inversePowerCircuit_cantor_cost_le_weight (k : ℕ) :
    (inversePowerCircuit.{u} k).cost ≤
      3574 * 2 ^ k * newtonCantorWeight k := by
  induction k with
  | zero =>
      rw [inversePowerCircuit_base_cost]
      norm_num [newtonCantorWeight]
  | succ k ih =>
      have hstep := inversePowerCircuit_cantor_step_le k
      have hmono := newtonCantorWeight_mono k
      have hterm := Nat.mul_le_mul_left (3574 * 2 ^ k) hmono
      calc
        (inversePowerCircuit.{u} (k + 1)).cost ≤
            (inversePowerCircuit.{u} k).cost +
              1787 * 2 ^ (k + 1) * (k + 3) * (Nat.log 2 (k + 3) + 2) := hstep
        _ ≤ 3574 * 2 ^ k * newtonCantorWeight k +
              1787 * 2 ^ (k + 1) * newtonCantorWeight (k + 1) := by
          apply Nat.add_le_add
          · exact ih
          · rw [newtonCantorWeight]
            have hk : k + 3 = k + 1 + 2 := by omega
            rw [hk]
            ring_nf
            exact le_rfl
        _ ≤ 3574 * 2 ^ (k + 1) * newtonCantorWeight (k + 1) := by
          rw [pow_succ]
          nlinarith [hterm]

theorem inversePowerCircuit_cantor_cost_le (k : ℕ) :
    (inversePowerCircuit.{u} k).cost ≤
      3574 * 2 ^ k * (k + 2) * (Nat.log 2 (k + 2) + 2) := by
  simpa [newtonCantorWeight, Nat.mul_assoc] using inversePowerCircuit_cantor_cost_le_weight k

private theorem newtonCantorWeight_padding_le {n : ℕ} (hn : 1 ≤ n) :
    2 ^ Nat.clog 2 n * newtonCantorWeight (Nat.clog 2 n) ≤
      2 * n * (Nat.log 2 (n + 1) + 3) *
        (Nat.log 2 (Nat.log 2 (n + 1) + 3) + 2) := by
  have hpad := (dyadicPadding_bounds hn).2
  have hlev := dyadicPadding_levels_bound hn
  have hk : Nat.clog 2 n + 2 ≤ Nat.log 2 (n + 1) + 3 := by omega
  have hlog := Nat.log_mono_right (b := 2) hk
  have hw : newtonCantorWeight (Nat.clog 2 n) ≤
      (Nat.log 2 (n + 1) + 3) *
        (Nat.log 2 (Nat.log 2 (n + 1) + 3) + 2) := by
    unfold newtonCantorWeight
    exact Nat.mul_le_mul hk (by omega)
  calc
    _ ≤ (2 * n) * ((Nat.log 2 (n + 1) + 3) *
          (Nat.log 2 (Nat.log 2 (n + 1) + 3) + 2)) := Nat.mul_le_mul hpad hw
    _ = _ := by ring

theorem seriesInverseCircuit_cantor_cost_le (n : ℕ) :
    (seriesInverseCircuit.{u} n).cost ≤
      7148 * n * (Nat.log 2 (n + 1) + 3) *
        (Nat.log 2 (Nat.log 2 (n + 1) + 3) + 2) := by
  by_cases hn : n = 0
  · simp [seriesInverseCircuit, hn]
  · have hnpos : 1 ≤ n := by omega
    simp only [seriesInverseCircuit, if_neg hn, Circuit.comp_cost, resize_cost,
      Nat.add_zero, Nat.zero_add]
    have hC := inversePowerCircuit_cantor_cost_le_weight (Nat.clog 2 n)
    have hpad := newtonCantorWeight_padding_le hnpos
    calc
      (inversePowerCircuit.{u} (Nat.clog 2 n)).cost ≤
          3574 * 2 ^ Nat.clog 2 n * newtonCantorWeight (Nat.clog 2 n) := hC
    _ ≤ 3574 * (2 * n * (Nat.log 2 (n + 1) + 3) *
            (Nat.log 2 (Nat.log 2 (n + 1) + 3) + 2)) := by
          simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 3574 hpad
      _ = _ := by ring

theorem fastSeriesInverse_cantor_cost_le (n : ℕ) :
    (fastSeriesInverse.{u} n).cost ≤
      7148 * n * (Nat.log 2 (n + 1) + 3) *
        (Nat.log 2 (Nat.log 2 (n + 1) + 3) + 2) := by
  simpa [fastSeriesInverse, NormalizedSeriesInverse.cost] using
    seriesInverseCircuit_cantor_cost_le n

private theorem newtonCantor_weight_le {a b : ℕ} (hab : a ≤ b) :
    a * (Nat.log 2 a + 2) ≤ b * (Nat.log 2 b + 2) := by
  apply Nat.mul_le_mul hab
  have hlog := Nat.log_mono_right (b := 2) hab
  omega

theorem fastMonicReduction_cantor_cost_le (n : ℕ) :
    (fastMonicReduction.{u} n).cost ≤
      8935 * n * (Nat.log 2 (2 * n + 2) + 3) *
        (Nat.log 2 (Nat.log 2 (2 * n + 2) + 3) + 2) := by
  let A := Nat.log 2 (2 * n + 2) + 3
  let L := Nat.log 2 (2 * n) + 1
  have hseries := seriesInverseCircuit_cantor_cost_le n
  have hmult := fastMultiplier_cantor_cost_le n
  have hA : Nat.log 2 (n + 1) + 3 ≤ A := by
    have hlog := Nat.log_mono_right (b := 2) (show n + 1 ≤ 2 * n + 2 by omega)
    dsimp [A]
    omega
  have hL : L ≤ A := by
    have hlog := Nat.log_mono_right (b := 2) (show 2 * n ≤ 2 * n + 2 by omega)
    dsimp [L, A]
    omega
  have hseriesWeight := newtonCantor_weight_le hA
  have hmultWeight := newtonCantor_weight_le hL
  have hApos : 1 ≤ A := by dsimp [A]; omega
  have hfactor : 2 ≤ A * (Nat.log 2 A + 2) := by
    have h := Nat.mul_le_mul hApos (show 2 ≤ Nat.log 2 A + 2 by omega)
    simpa using h
  change (monicReductionCircuit.{u} n).cost ≤ _
  rw [monicReductionCircuit_cost]
  have hSeries' : (seriesInverseCircuit.{u} n).cost ≤
      7148 * n * (A * (Nat.log 2 A + 2)) := by
    calc
      _ ≤ 7148 * n * ((Nat.log 2 (n + 1) + 3) *
          (Nat.log 2 (Nat.log 2 (n + 1) + 3) + 2)) := by
        simpa [Nat.mul_assoc] using hseries
      _ ≤ _ := Nat.mul_le_mul_left (7148 * n) hseriesWeight
  have hMult' : (fastMultiplier.{u} n).cost ≤
      893 * n * (A * (Nat.log 2 A + 2)) := by
    calc
      _ ≤ 893 * n * (L * (Nat.log 2 L + 2)) := by
        simpa [L, Nat.mul_assoc] using hmult
      _ ≤ _ := Nat.mul_le_mul_left (893 * n) hmultWeight
  have hSeriesFast' : (fastSeriesInverse.{u} n).cost ≤
      7148 * n * (A * (Nat.log 2 A + 2)) := by
    simpa [fastSeriesInverse, NormalizedSeriesInverse.cost] using hSeries'
  have hbound : (fastSeriesInverse.{u} n).cost +
      2 * (fastMultiplier.{u} n).cost + 2 * n ≤
      8935 * n * (A * (Nat.log 2 A + 2)) := by
    nlinarith [hSeriesFast', Nat.mul_le_mul_left n hfactor]
  simpa [A, Nat.mul_assoc] using hbound

end DivisionFree.PolynomialArithmetic
