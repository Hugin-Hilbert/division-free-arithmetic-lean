import DivisionFree.Polynomial.CantorMultiplication
import DivisionFree.Polynomial.MonicReduction

/-! Multiplication-gate bounds for Newton inversion and monic reduction.
These count the gates in the actual recursive circuits. -/

namespace DivisionFree.PolynomialArithmetic

universe u

theorem twoMinus_multiplications (n : ℕ) : (twoMinus n).multiplications = 0 := by
  classical
  unfold twoMinus
  simp only [Circuit.comp_multiplications, Circuit.bundle_multiplications,
    Circuit.wire_multiplications]
  rw [Nat.add_zero]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases h : i.val = 0 <;> simp [h]

theorem newtonStepCircuit_multiplications {n : ℕ} (A : Multiplier.{u} n) :
    (newtonStepCircuit A).multiplications = 2 * A.circuit.multiplications := by
  simp [newtonStepCircuit, twoMinus_multiplications]
  omega

theorem fastMultiplier_multiplications_le (n : ℕ) :
    (fastMultiplier.{u} n).circuit.multiplications ≤
      390 * n * (Nat.log 2 (2 * n) + 1) := by
  have h := fastFullMultiplier_multiplications_le.{u} n
  simpa [fastMultiplier, FullMultiplier.truncate, Circuit.comp_multiplications] using h

theorem quotientFromInverse_multiplications (n : ℕ) :
    (quotientFromInverse.{u} n).multiplications =
      (fastMultiplier.{u} n).circuit.multiplications := by
  simp [quotientFromInverse, highReverse, reverseVector,
    Circuit.comp_multiplications]

theorem vectorSub_multiplications (n : ℕ) : (vectorSub n).multiplications = 0 := by
  classical
  simp [vectorSub, Circuit.multiplications]

theorem preparedRemainder_multiplications (n : ℕ) :
    (preparedRemainder.{u} n).multiplications =
      2 * (fastMultiplier.{u} n).circuit.multiplications := by
  simp [preparedRemainder, quotientFromInverse_multiplications,
    vectorSub_multiplications, Circuit.comp_multiplications]
  omega

theorem monicPrepare_multiplications (n : ℕ) :
    (monicPrepare.{u} n).multiplications =
      (fastSeriesInverse.{u} n).circuit.multiplications := by
  simp [monicPrepare, reverseMonicPrefix_multiplications,
    Circuit.comp_multiplications]

theorem monicReductionCircuit_multiplications (n : ℕ) :
    (monicReductionCircuit.{u} n).multiplications =
      (fastSeriesInverse.{u} n).circuit.multiplications +
        2 * (fastMultiplier.{u} n).circuit.multiplications := by
  simp [monicReductionCircuit, monicPrepare_multiplications,
    preparedRemainder_multiplications, Circuit.comp_multiplications]

@[simp] theorem inversePowerCircuit_base_multiplications :
    (inversePowerCircuit.{u} 0).multiplications = 0 := by
  simp [inversePowerCircuit]

theorem inversePowerCircuit_step_multiplications (k : ℕ) :
    (inversePowerCircuit.{u} (k + 1)).multiplications =
      (inversePowerCircuit.{u} k).multiplications +
        2 * (fastMultiplier.{u} (2 ^ (k + 1))).circuit.multiplications := by
  simp only [inversePowerCircuit, Circuit.comp_multiplications,
    Circuit.pair_multiplications, Circuit.wire_multiplications,
    resize_multiplications, newtonStepCircuit_multiplications]
  omega

theorem inversePowerCircuit_multiplications_le (k : ℕ) :
    (inversePowerCircuit.{u} k).multiplications ≤ 1560 * 2 ^ k * (k + 2) := by
  induction k with
  | zero => norm_num [inversePowerCircuit_base_multiplications]
  | succ k ih =>
      rw [inversePowerCircuit_step_multiplications]
      have hm := fastMultiplier_multiplications_le (2 ^ (k + 1))
      have hlog : Nat.log 2 (2 * 2 ^ (k + 1)) = k + 2 := by
        rw [← pow_succ', Nat.log_pow (by decide)]
      rw [hlog] at hm
      calc
        _ ≤ 1560 * 2 ^ k * (k + 2) +
            2 * (390 * 2 ^ (k + 1) * (k + 3)) := by
          exact Nat.add_le_add ih (Nat.mul_le_mul_left 2 hm)
        _ ≤ 1560 * 2 ^ (k + 1) * (k + 3) := by
          rw [pow_succ]
          nlinarith [Nat.one_le_pow k 2 (by decide : 0 < 2)]

theorem fastSeriesInverse_cantor_multiplications_le (n : ℕ) :
    (fastSeriesInverse.{u} n).circuit.multiplications ≤
      3120 * n * (Nat.log 2 (n + 1) + 3) := by
  by_cases hn : n = 0
  · simp [fastSeriesInverse, seriesInverseCircuit, hn]
  · have hnpos : 1 ≤ n := by omega
    have hpad := (dyadicPadding_bounds hnpos).2
    have hlev := dyadicPadding_levels_bound hnpos
    have hrec := inversePowerCircuit_multiplications_le (Nat.clog 2 n)
    have hsize : 2 ^ Nat.clog 2 n * (Nat.clog 2 n + 2) ≤
        (2 * n) * (Nat.log 2 (n + 1) + 3) := by
      exact Nat.mul_le_mul hpad (by omega)
    have heq : (fastSeriesInverse.{u} n).circuit.multiplications =
        (inversePowerCircuit.{u} (Nat.clog 2 n)).multiplications := by
      simp [fastSeriesInverse, seriesInverseCircuit, hn, resize_multiplications]
    rw [heq]
    calc
      _ ≤ 1560 * 2 ^ Nat.clog 2 n * (Nat.clog 2 n + 2) := hrec
      _ ≤ 1560 * ((2 * n) * (Nat.log 2 (n + 1) + 3)) := by
        calc
          _ = 1560 * (2 ^ Nat.clog 2 n * (Nat.clog 2 n + 2)) := by ring
          _ ≤ 1560 * ((2 * n) * (Nat.log 2 (n + 1) + 3)) :=
            Nat.mul_le_mul_left 1560 hsize
      _ = 3120 * n * (Nat.log 2 (n + 1) + 3) := by ring

theorem fastMonicReduction_cantor_multiplications_le (n : ℕ) :
    (fastMonicReduction.{u} n).circuit.multiplications ≤
      3900 * n * (Nat.log 2 (2 * n + 2) + 3) := by
  have hi := fastSeriesInverse_cantor_multiplications_le.{u} n
  have hm := fastMultiplier_multiplications_le n
  have hlog₁ : Nat.log 2 (n + 1) ≤ Nat.log 2 (2 * n + 2) :=
    Nat.log_mono_right (by omega)
  have hlog₂ : Nat.log 2 (2 * n) ≤ Nat.log 2 (2 * n + 2) :=
    Nat.log_mono_right (by omega)
  change (monicReductionCircuit.{u} n).multiplications ≤ _
  rw [monicReductionCircuit_multiplications]
  have hseries : (fastSeriesInverse.{u} n).circuit.multiplications ≤
      3120 * n * (Nat.log 2 (2 * n + 2) + 3) := by
    exact hi.trans (Nat.mul_le_mul_left (3120 * n) (by omega))
  have hmult : (fastMultiplier.{u} n).circuit.multiplications ≤
      390 * n * (Nat.log 2 (2 * n + 2) + 3) := by
    exact hm.trans (Nat.mul_le_mul_left (390 * n) (by omega))
  nlinarith

end DivisionFree.PolynomialArithmetic
