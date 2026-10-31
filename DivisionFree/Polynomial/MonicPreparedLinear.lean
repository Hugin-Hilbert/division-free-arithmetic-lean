import DivisionFree.Circuit.Linearization
import DivisionFree.Polynomial.MonicReduction
import DivisionFree.Polynomial.CantorNewtonCost
import DivisionFree.Polynomial.CantorNewtonResources

/-! Actual prepared linear programs and transposes for monic reduction.
The modulus preparation, including the reflected inverse, is retained in the
parameter circuit. -/

namespace DivisionFree.PolynomialArithmetic

open DivisionFree
open DivisionFree.Circuit

universe u

private theorem vectorPolynomial_scale {R : Type*} [CommRing R]
    (k : ℕ) (r : R) (x : Fin k → R) :
    vectorPolynomial k (fun i => r * x i) = Polynomial.C r * vectorPolynomial k x := by
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < k
  · rw [vectorPolynomial_coeff_of_lt k i _ hi,
      Polynomial.coeff_C_mul, vectorPolynomial_coeff_of_lt k i x hi]
  · have hki : k ≤ i := Nat.le_of_not_gt hi
    rw [vectorPolynomial_coeff_eq_zero_of_ge k i _ hki,
      Polynomial.coeff_C_mul, vectorPolynomial_coeff_eq_zero_of_ge k i x hki]
    simp

/-- The output is linear in the dividend over every coefficient ring. -/
theorem monicReductionCircuit_rightHomogeneous (n : ℕ) :
    Circuit.RightHomogeneous.{u} (monicReductionCircuit.{u} n) := by
  intro R _ a r h
  apply vectorPolynomial_injective n
  have hscaled := monicReductionCircuit_correct (R := R) n a (fun i => r * h i)
  have hbase := monicReductionCircuit_correct (R := R) n a h
  have hinput : vectorPolynomial (2 * n) (fun i => r * h i) =
      r • vectorPolynomial (2 * n) h := by
    rw [vectorPolynomial_scale, Polynomial.smul_eq_C_mul]
  calc
    vectorPolynomial n
        ((monicReductionCircuit.{u} n).eval (Sum.elim a (fun i => r * h i))) =
        vectorPolynomial (2 * n) (fun i => r * h i) %ₘ monicPolynomial n a := hscaled
    _ = r • (vectorPolynomial (2 * n) h %ₘ monicPolynomial n a) := by
      rw [hinput]
      exact (Polynomial.modByMonicHom (monicPolynomial n a)).map_smul r _
    _ = r • vectorPolynomial n
          ((monicReductionCircuit.{u} n).eval (Sum.elim a h)) := by rw [hbase]
    _ = vectorPolynomial n (fun i =>
          r * (monicReductionCircuit.{u} n).eval (Sum.elim a h) i) := by
      rw [vectorPolynomial_scale, Polynomial.smul_eq_C_mul]

/-- Evaluate the monic-modulus preparation once, retaining all operands of
the reduction circuit at dividend zero. -/
noncomputable def monicReductionParameterPreparation (n : ℕ) :
    Circuit (Fin n) (Fin (Fintype.card (monicReductionCircuit.{u} n).Tape)) :=
  Circuit.parameterPreparation.{u} (monicReductionCircuit.{u} n)

/-- The actual linear program on the full dividend after modulus preparation. -/
noncomputable def monicReductionLinearizedProgram (n : ℕ) :
    LinearStraightLine.Program (Fintype.card (monicReductionCircuit.{u} n).Tape)
      (2 * n) n :=
  Circuit.linearizedProgram.{u} (monicReductionCircuit.{u} n)

/-- Compile the prepared forward reduction to the circuit syntax. -/
noncomputable def monicReductionPreparedForward (n : ℕ) :
    Circuit (Fin n ⊕ Fin (2 * n)) (Fin n) :=
  Circuit.preparedForward.{u} (monicReductionCircuit.{u} n)

/-- Transpose the dividend-to-remainder linear map, with modulus preparation
executed once before the transposed program. -/
noncomputable def monicReductionPreparedTranspose (n : ℕ) :
    Circuit (Fin n ⊕ Fin n) (Fin (2 * n)) :=
  Circuit.preparedTranspose.{u} (monicReductionCircuit.{u} n)

theorem monicReductionParameterPreparation_eval {R : Type u} [Ring R]
    (n : ℕ) (a : Fin n → R) (j : Fin (Fintype.card (monicReductionCircuit.{u} n).Tape)) :
    (monicReductionParameterPreparation.{u} n).eval a j =
      (monicReductionCircuit.{u} n).tapeValues
        (Sum.elim a (fun _ => 0)) ((Fintype.equivFin (monicReductionCircuit.{u} n).Tape).symm j) :=
  Circuit.parameterPreparation_eval (monicReductionCircuit.{u} n) a j

theorem monicReductionLinearizedProgram_correct {R : Type u} [CommRing R]
    (n : ℕ) (a : Fin n → R) (h : Fin (2 * n) → R) :
    (monicReductionLinearizedProgram.{u} n).eval
        ((monicReductionParameterPreparation.{u} n).eval a) h =
      (monicReductionCircuit.{u} n).eval (Sum.elim a h) :=
  Circuit.linearizedProgram_correct (monicReductionCircuit.{u} n)
    (monicReductionCircuit_rightHomogeneous n) a h

theorem monicReductionLinearizedProgram_polynomial_correct {R : Type u} [CommRing R]
    (n : ℕ) (a : Fin n → R) (h : Fin (2 * n) → R) :
    vectorPolynomial n ((monicReductionLinearizedProgram.{u} n).eval
      ((monicReductionParameterPreparation.{u} n).eval a) h) =
      vectorPolynomial (2 * n) h %ₘ monicPolynomial n a := by
  rw [monicReductionLinearizedProgram_correct]
  exact monicReductionCircuit_correct n a h

theorem monicReductionPreparedForward_correct {R : Type u} [CommRing R]
    (n : ℕ) (a : Fin n → R) (h : Fin (2 * n) → R) :
    (monicReductionPreparedForward.{u} n).eval (Sum.elim a h) =
      (monicReductionCircuit.{u} n).eval (Sum.elim a h) :=
  Circuit.preparedForward_correct (monicReductionCircuit.{u} n)
    (monicReductionCircuit_rightHomogeneous n) a h

theorem monicReductionPreparedForward_polynomial_correct {R : Type u} [CommRing R]
    (n : ℕ) (a : Fin n → R) (h : Fin (2 * n) → R) :
    vectorPolynomial n ((monicReductionPreparedForward.{u} n).eval (Sum.elim a h)) =
      vectorPolynomial (2 * n) h %ₘ monicPolynomial n a := by
  rw [monicReductionPreparedForward_correct]
  exact monicReductionCircuit_correct n a h

theorem monicReductionPreparedTranspose_adjoint {R : Type u} [CommRing R]
    (n : ℕ) (a : Fin n → R) (h : Fin (2 * n) → R) (y : Fin n → R) :
    (monicReductionCircuit.{u} n).eval (Sum.elim a h) ⬝ᵥ y =
      h ⬝ᵥ (monicReductionPreparedTranspose.{u} n).eval (Sum.elim a y) :=
  Circuit.preparedTranspose_adjoint (monicReductionCircuit.{u} n)
    (monicReductionCircuit_rightHomogeneous n) a h y

theorem monicReductionParameterPreparation_cost (n : ℕ) :
    (monicReductionParameterPreparation.{u} n).cost =
      (fastMonicReduction.{u} n).cost := by
  change (Circuit.parameterPreparation.{u} (monicReductionCircuit.{u} n)).cost = _
  rw [Circuit.parameterPreparation_cost]
  rfl

theorem monicReductionParameterPreparation_constantBits (n : ℕ) :
    (monicReductionParameterPreparation.{u} n).constantBits =
      (fastMonicReduction.{u} n).circuit.constantBits := by
  change (Circuit.parameterPreparation.{u} (monicReductionCircuit.{u} n)).constantBits = _
  rw [Circuit.parameterPreparation_constantBits]
  rfl

theorem monicReductionPreparedForward_cost_le (n : ℕ) :
    (monicReductionPreparedForward.{u} n).cost ≤
      4 * (fastMonicReduction.{u} n).cost := by
  change (Circuit.preparedForward.{u} (monicReductionCircuit.{u} n)).cost ≤
    4 * (monicReductionCircuit.{u} n).cost
  exact Circuit.preparedForward_cost_le (monicReductionCircuit.{u} n)

theorem monicReductionPreparedTranspose_cost_le (n : ℕ) :
    (monicReductionPreparedTranspose.{u} n).cost ≤
      7 * (fastMonicReduction.{u} n).cost + n := by
  change (Circuit.preparedTranspose.{u} (monicReductionCircuit.{u} n)).cost ≤
    7 * (monicReductionCircuit.{u} n).cost + n
  exact Circuit.preparedTranspose_cost_le (monicReductionCircuit.{u} n)

/-- Keep multiplication gates separate when bounding the prepared circuits. -/
theorem monicReductionPreparedForward_cost_refined (n : ℕ) :
    (monicReductionPreparedForward.{u} n).cost =
      2 * (fastMonicReduction.{u} n).cost +
        2 * (fastMonicReduction.{u} n).circuit.multiplications := by
  simp only [monicReductionPreparedForward, Circuit.preparedForward,
    Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost, Nat.zero_add,
    Nat.add_zero, Circuit.parameterPreparation_cost,
    LinearStraightLine.Program.compile_cost, Circuit.linearizedProgram_cost]
  change _ = 2 * (monicReductionCircuit.{u} n).cost +
    2 * (monicReductionCircuit.{u} n).multiplications
  unfold Circuit.cost
  omega

theorem monicReductionPreparedTranspose_cost_refined (n : ℕ) :
    (monicReductionPreparedTranspose.{u} n).cost ≤
      3 * (fastMonicReduction.{u} n).cost +
        4 * (fastMonicReduction.{u} n).circuit.multiplications + n := by
  have ht := (Circuit.linearizedProgram.{u} (monicReductionCircuit.{u} n)).transposeCircuit_cost
  rw [Circuit.linearizedProgram_cost] at ht
  simp only [monicReductionPreparedTranspose, Circuit.preparedTranspose,
    Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost, Nat.zero_add,
    Nat.add_zero, Circuit.parameterPreparation_cost]
  change _ ≤ 3 * (monicReductionCircuit.{u} n).cost +
    4 * (monicReductionCircuit.{u} n).multiplications + n
  unfold Circuit.cost at ht ⊢
  omega

private theorem monic_log_scale_four (n : ℕ) :
    4 * (n * (Nat.log 2 (2 * n + 2) + 3)) ≤
      (n * (Nat.log 2 (2 * n + 2) + 3)) *
        (Nat.log 2 (Nat.log 2 (2 * n + 2) + 3) + 2) := by
  have hfirst : 0 < Nat.log 2 (2 * n + 2) := Nat.log_pos (by omega) (by omega)
  have hsecond : 2 ≤ Nat.log 2 (Nat.log 2 (2 * n + 2) + 3) :=
    Nat.le_log_of_pow_le (by omega) (by norm_num; omega)
  simpa only [Nat.mul_comm 4] using
    (Nat.mul_le_mul_left (n * (Nat.log 2 (2 * n + 2) + 3))
      (show 4 ≤ Nat.log 2 (Nat.log 2 (2 * n + 2) + 3) + 2 by omega))

theorem monicReductionPreparedForward_cantor_cost_le (n : ℕ) :
    (monicReductionPreparedForward.{u} n).cost ≤
      19820 * n * (Nat.log 2 (2 * n + 2) + 3) *
        (Nat.log 2 (Nat.log 2 (2 * n + 2) + 3) + 2) := by
  have h := monicReductionPreparedForward_cost_refined.{u} n
  have hc := fastMonicReduction_cantor_cost_le.{u} n
  have hm := fastMonicReduction_cantor_multiplications_le.{u} n
  have hscale := monic_log_scale_four n
  nlinarith

theorem monicReductionPreparedTranspose_cantor_cost_le (n : ℕ) :
    (monicReductionPreparedTranspose.{u} n).cost ≤
      30705 * n * (Nat.log 2 (2 * n + 2) + 3) *
        (Nat.log 2 (Nat.log 2 (2 * n + 2) + 3) + 2) + n := by
  have h := monicReductionPreparedTranspose_cost_refined.{u} n
  have hc := fastMonicReduction_cantor_cost_le.{u} n
  have hm := fastMonicReduction_cantor_multiplications_le.{u} n
  have hscale := monic_log_scale_four n
  nlinarith

theorem monicReductionPreparedForward_constantBits_le (n : ℕ) :
    (monicReductionPreparedForward.{u} n).constantBits ≤
      300 * n * (Nat.log 2 (2 * n + 2) + 3) + 2 := by
  change (Circuit.preparedForward.{u} (monicReductionCircuit.{u} n)).constantBits ≤ _
  rw [Circuit.preparedForward_constantBits]
  exact fastMonicReduction_constantBits_le n

theorem monicReductionPreparedTranspose_constantBits_le (n : ℕ) :
    (monicReductionPreparedTranspose.{u} n).constantBits ≤
      300 * n * (Nat.log 2 (2 * n + 2) + 3) + 2 := by
  change (Circuit.preparedTranspose.{u} (monicReductionCircuit.{u} n)).constantBits ≤ _
  rw [Circuit.preparedTranspose_constantBits]
  exact fastMonicReduction_constantBits_le n

theorem monicReductionParameterPreparation_multiplications (n : ℕ) :
    (monicReductionParameterPreparation.{u} n).multiplications =
      (monicReductionCircuit.{u} n).multiplications :=
  Circuit.parameterPreparation_multiplications (monicReductionCircuit.{u} n)

theorem monicReductionLinearizedProgram_multiplications (n : ℕ) :
    (monicReductionLinearizedProgram.{u} n).compile.multiplications =
      2 * (monicReductionCircuit.{u} n).multiplications :=
  Circuit.linearizedProgram_multiplications (monicReductionCircuit.{u} n)

theorem monicReductionPreparedForward_multiplications (n : ℕ) :
    (monicReductionPreparedForward.{u} n).multiplications =
      3 * (monicReductionCircuit.{u} n).multiplications :=
  Circuit.preparedForward_multiplications (monicReductionCircuit.{u} n)

theorem monicReductionPreparedTranspose_multiplications (n : ℕ) :
    (monicReductionPreparedTranspose.{u} n).multiplications =
      3 * (monicReductionCircuit.{u} n).multiplications :=
  Circuit.preparedTranspose_multiplications (monicReductionCircuit.{u} n)

end DivisionFree.PolynomialArithmetic
