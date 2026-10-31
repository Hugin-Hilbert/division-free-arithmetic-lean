import DivisionFree.Circuit.Prepare
import DivisionFree.Circuit.Differential
import DivisionFree.LinearCircuit.Compile
import DivisionFree.LinearStraightLine.MultiplicationCount

/-! Prepare actual multiplication operands at a fixed parameter value and
compile the resulting linear map to a transposable straight-line program.
No scalar parameter is supplied by an unchecked external provider. -/

namespace DivisionFree.Circuit

open Matrix

universe u

variable {P : Type} [Fintype P] {n m : ℕ}

/-- Evaluate the original circuit at zero in its vector variables, retaining
all multiplication operands as explicit prepared scalar parameters. -/
noncomputable def parameterPreparation (C : Circuit (P ⊕ Fin n) (Fin m)) :
    Circuit P (Fin (Fintype.card C.Tape)) :=
  .comp (.pair (.wire id) (.zero : Circuit P (Fin n)))
    (.comp (prepare.{u} C).circuit
      (.wire fun j => Sum.inr ((Fintype.equivFin C.Tape).symm j)))

theorem parameterPreparation_cost (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (parameterPreparation.{u} C).cost = C.cost := by
  simp only [parameterPreparation, comp_cost, pair_cost, wire_cost, zero_cost,
    Nat.zero_add, Nat.add_zero]
  exact (prepare.{u} C).cost_eq

theorem parameterPreparation_multiplications (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (parameterPreparation.{u} C).multiplications = C.multiplications := by
  simp only [parameterPreparation, comp_multiplications, pair_multiplications,
    wire_multiplications, zero_multiplications, Nat.zero_add, Nat.add_zero]
  exact (prepare.{u} C).multiplications_eq

theorem parameterPreparation_constantBits (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (parameterPreparation.{u} C).constantBits = C.constantBits := by
  simp only [parameterPreparation, comp_constantBits, constantBits,
    Nat.zero_add, Nat.add_zero]
  exact (prepare.{u} C).constantBits_eq

theorem parameterPreparation_eval (C : Circuit (P ⊕ Fin n) (Fin m))
    {R : Type u} [Ring R] (a : P → R) (j : Fin (Fintype.card C.Tape)) :
    (parameterPreparation.{u} C).eval a j =
      C.tapeValues (Sum.elim a (fun _ => 0)) ((Fintype.equivFin C.Tape).symm j) := by
  simp only [parameterPreparation, eval_comp_function, eval_pair_function,
    eval_wire_function, eval_zero_function]
  exact congrFun ((prepare.{u} C).correct R (Sum.elim a (fun _ => 0)))
    (Sum.inr ((Fintype.equivFin C.Tape).symm j))

/-- The linear syntax sees the original parameter inputs as zero directions. -/
noncomputable def linearizedSyntax (C : Circuit (P ⊕ Fin n) (Fin m)) :
    LinearCircuit (Fin (Fintype.card C.Tape)) (Fin n) (Fin m) :=
  .comp (.pair .zero (.wire id))
    (LinearCircuit.mapParams (Fintype.equivFin C.Tape) C.differential)

theorem linearizedSyntax_cost (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (linearizedSyntax C).cost = C.additions + C.negations + 3 * C.multiplications := by
  simp only [linearizedSyntax, LinearCircuit.cost, LinearCircuit.cost_mapParams,
    differential_cost, Nat.zero_add]

theorem linearizedSyntax_multiplications (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (linearizedSyntax C).multiplications = 2 * C.multiplications := by
  simp only [linearizedSyntax, LinearCircuit.multiplications,
    LinearCircuit.multiplications_mapParams, differential_multiplications, Nat.zero_add]

noncomputable def linearizedProgram (C : Circuit (P ⊕ Fin n) (Fin m)) :
    LinearStraightLine.Program (Fintype.card C.Tape) n m :=
  LinearCircuit.toProgram.{u} (linearizedSyntax C)

theorem linearizedProgram_cost (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (linearizedProgram.{u} C).cost = C.additions + C.negations + 3 * C.multiplications := by
  rw [linearizedProgram, LinearCircuit.toProgram_cost, linearizedSyntax_cost]

theorem linearizedProgram_multiplications (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (linearizedProgram.{u} C).compile.multiplications = 2 * C.multiplications := by
  rw [linearizedProgram, LinearCircuit.toProgram_compile_multiplications,
    linearizedSyntax_multiplications]

theorem linearizedProgram_eval (C : Circuit (P ⊕ Fin n) (Fin m))
    {R : Type u} [CommRing R] (a : P → R) (x : Fin n → R) :
    (linearizedProgram.{u} C).eval ((parameterPreparation.{u} C).eval a) x =
      C.differential.eval (C.tapeValues (Sum.elim a (fun _ => 0)))
        (Sum.elim (fun _ => 0) x) := by
  rw [linearizedProgram, LinearCircuit.toProgram_eval]
  change (LinearCircuit.mapParams (Fintype.equivFin C.Tape) C.differential).eval
    ((parameterPreparation.{u} C).eval a) (Sum.elim (fun _ => 0) x) = _
  have hp : ((parameterPreparation.{u} C).eval a) ∘ (Fintype.equivFin C.Tape) =
      C.tapeValues (Sum.elim a (fun _ => 0)) := by
    funext t
    simp only [Function.comp_apply, parameterPreparation_eval, Equiv.symm_apply_apply]
  rw [LinearCircuit.eval_mapParams, hp]

/-- Polynomial inputs used to extract precisely the first-order vector part. -/
noncomputable def linearizationInput {R : Type*} [CommRing R] (a : P → R) (x : Fin n → R) :
    P ⊕ Fin n → Polynomial R :=
  Sum.elim (fun p => Polynomial.C (a p)) (fun i => Polynomial.C (x i) * Polynomial.X)

theorem linearizedProgram_coeff_one (C : Circuit (P ⊕ Fin n) (Fin m))
    {R : Type u} [CommRing R] (a : P → R) (x : Fin n → R) (j : Fin m) :
    (linearizedProgram.{u} C).eval ((parameterPreparation.{u} C).eval a) x j =
      (C.eval (linearizationInput a x) j).coeff 1 := by
  rw [linearizedProgram_eval, differential_eval_coeff_one]
  have hz : (fun i => (linearizationInput a x i).coeff 0) = Sum.elim a (fun _ => 0) := by
    funext i
    cases i <;> simp [linearizationInput]
  have ho : (fun i => (linearizationInput a x i).coeff 1) = Sum.elim (fun _ => 0) x := by
    funext i
    cases i <;> simp [linearizationInput]
  rw [hz, ho]

/-- A universal scalar-homogeneity law suffices for the extraction to equal
the original circuit, since it also applies over polynomial coefficient rings. -/
def RightHomogeneous (C : Circuit (P ⊕ Fin n) (Fin m)) : Prop :=
  ∀ (R : Type u) [CommRing R] (a : P → R) (r : R) (x : Fin n → R),
    C.eval (Sum.elim a (fun i => r * x i)) = fun j => r * C.eval (Sum.elim a x) j

omit [Fintype P] in
theorem coeff_one_of_homogeneous (C : Circuit (P ⊕ Fin n) (Fin m))
    (hC : RightHomogeneous.{u} C) {R : Type u} [CommRing R]
    (a : P → R) (x : Fin n → R) (j : Fin m) :
    (C.eval (linearizationInput a x) j).coeff 1 = C.eval (Sum.elim a x) j := by
  have h := congrFun (hC (Polynomial R) (fun p => Polynomial.C (a p)) Polynomial.X
    (fun i => Polynomial.C (x i))) j
  have hin : (Sum.elim (fun p => Polynomial.C (a p))
      (fun i => Polynomial.X * Polynomial.C (x i))) = linearizationInput a x := by
    funext i
    cases i with
    | inl p => rfl
    | inr i => exact mul_comm _ _
  rw [hin] at h
  have hmap : C.eval (Sum.elim (fun p => Polynomial.C (a p)) (fun i => Polynomial.C (x i))) j =
      Polynomial.C (C.eval (Sum.elim a x) j) := by
    have hfun : (fun i => Polynomial.C (Sum.elim a x i)) =
        Sum.elim (fun p => Polynomial.C (a p)) (fun i => Polynomial.C (x i)) := by
      funext i
      cases i <;> rfl
    simpa only [hfun] using
      (eval_map Polynomial.C C (Sum.elim a x) j).symm
  rw [h, hmap]
  simp

theorem linearizedProgram_correct (C : Circuit (P ⊕ Fin n) (Fin m))
    (hC : RightHomogeneous.{u} C) {R : Type u} [CommRing R]
    (a : P → R) (x : Fin n → R) :
    (linearizedProgram.{u} C).eval ((parameterPreparation.{u} C).eval a) x =
      C.eval (Sum.elim a x) := by
  funext j
  rw [linearizedProgram_coeff_one, coeff_one_of_homogeneous C hC]

/-- Prepare coefficients once and then execute the extracted forward program. -/
noncomputable def preparedForward (C : Circuit (P ⊕ Fin n) (Fin m)) :
    Circuit (P ⊕ Fin n) (Fin m) :=
  .comp (.pair (.comp (.wire Sum.inl) (parameterPreparation.{u} C)) (.wire Sum.inr))
    (linearizedProgram.{u} C).compile

theorem preparedForward_cost_le (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (preparedForward.{u} C).cost ≤ 4 * C.cost := by
  simp only [preparedForward, comp_cost, pair_cost, wire_cost, Nat.zero_add,
    Nat.add_zero, parameterPreparation_cost, LinearStraightLine.Program.compile_cost,
    linearizedProgram_cost]
  unfold cost
  omega

theorem preparedForward_multiplications (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (preparedForward.{u} C).multiplications = 3 * C.multiplications := by
  simp only [preparedForward, comp_multiplications, pair_multiplications,
    wire_multiplications, Nat.zero_add, Nat.add_zero, parameterPreparation_multiplications,
    linearizedProgram_multiplications]
  omega

theorem preparedForward_constantBits (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (preparedForward.{u} C).constantBits = C.constantBits := by
  simp only [preparedForward, comp_constantBits, constantBits, Nat.zero_add,
    Nat.add_zero, parameterPreparation_constantBits,
    LinearStraightLine.Program.compile_constantBits]

theorem preparedForward_correct (C : Circuit (P ⊕ Fin n) (Fin m))
    (hC : RightHomogeneous.{u} C) {R : Type u} [CommRing R]
    (a : P → R) (x : Fin n → R) :
    (preparedForward.{u} C).eval (Sum.elim a x) = C.eval (Sum.elim a x) := by
  simp only [preparedForward, eval_comp_function, eval_pair_function,
    eval_wire_function, Sum.elim_inl, Sum.elim_inr,
    LinearStraightLine.Program.compile_eval]
  exact linearizedProgram_correct C hC a x

/-- Preparation is executed once before the transposed straight-line program. -/
noncomputable def preparedTranspose (C : Circuit (P ⊕ Fin n) (Fin m)) :
    Circuit (P ⊕ Fin m) (Fin n) :=
  .comp (.pair (.comp (.wire Sum.inl) (parameterPreparation.{u} C)) (.wire Sum.inr))
    (linearizedProgram.{u} C).transposeCircuit

theorem preparedTranspose_cost_le (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (preparedTranspose.{u} C).cost ≤ 7 * C.cost + m := by
  have ht := (linearizedProgram.{u} C).transposeCircuit_cost
  rw [linearizedProgram_cost] at ht
  simp only [preparedTranspose, comp_cost, pair_cost, wire_cost, Nat.zero_add,
    Nat.add_zero, parameterPreparation_cost]
  unfold cost at ht ⊢
  omega

theorem preparedTranspose_multiplications (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (preparedTranspose.{u} C).multiplications = 3 * C.multiplications := by
  simp only [preparedTranspose, comp_multiplications, pair_multiplications,
    wire_multiplications, Nat.zero_add, Nat.add_zero, parameterPreparation_multiplications,
    LinearStraightLine.Program.transposeCircuit_multiplications,
    linearizedProgram_multiplications]
  omega

theorem preparedTranspose_constantBits (C : Circuit (P ⊕ Fin n) (Fin m)) :
    (preparedTranspose.{u} C).constantBits = C.constantBits := by
  simp only [preparedTranspose, comp_constantBits, constantBits, Nat.zero_add,
    Nat.add_zero, parameterPreparation_constantBits,
    LinearStraightLine.Program.transposeCircuit_constantBits]

theorem preparedTranspose_eval (C : Circuit (P ⊕ Fin n) (Fin m))
    {R : Type u} [CommRing R] (a : P → R) (y : Fin m → R) :
    (preparedTranspose.{u} C).eval (Sum.elim a y) =
      (linearizedProgram.{u} C).transposeCircuit.eval
        (Sum.elim ((parameterPreparation.{u} C).eval a) y) := by
  simp only [preparedTranspose, eval_comp_function, eval_pair_function,
    eval_wire_function, Sum.elim_inl, Sum.elim_inr]

theorem preparedTranspose_adjoint (C : Circuit (P ⊕ Fin n) (Fin m))
    (hC : RightHomogeneous.{u} C) {R : Type u} [CommRing R]
    (a : P → R) (x : Fin n → R) (y : Fin m → R) :
    C.eval (Sum.elim a x) ⬝ᵥ y = x ⬝ᵥ (preparedTranspose.{u} C).eval (Sum.elim a y) := by
  rw [← linearizedProgram_correct C hC a x, preparedTranspose_eval]
  exact (linearizedProgram.{u} C).transposeCircuit_adjoint _ x y

end DivisionFree.Circuit
