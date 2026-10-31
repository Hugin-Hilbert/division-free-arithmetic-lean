import DivisionFree.Circuit.Linearization
import DivisionFree.Polynomial.CantorMultiplication

/-! Prepared first-order programs and transposes for the actual full multiplier. -/

namespace DivisionFree.PolynomialArithmetic

open DivisionFree
open DivisionFree.Circuit

universe u

variable {n : ℕ}

/-- Split the Boolean-tagged inputs of a full multiplier into a fixed left
factor and a variable right factor. -/
def FullMultiplier.splitCircuit (A : FullMultiplier.{u} n) :
    Circuit (Fin n ⊕ Fin n) (Fin (2 * n)) :=
  .comp (.wire (fun z : Bool × Fin n => if z.1 then Sum.inr z.2 else Sum.inl z.2))
    A.circuit

theorem FullMultiplier.splitCircuit_cost (A : FullMultiplier.{u} n) :
    (A.splitCircuit).cost = A.cost := by
  simp [FullMultiplier.splitCircuit, FullMultiplier.cost]

theorem FullMultiplier.splitCircuit_multiplications (A : FullMultiplier.{u} n) :
    (A.splitCircuit).multiplications = A.circuit.multiplications := by
  simp [FullMultiplier.splitCircuit]

theorem FullMultiplier.splitCircuit_constantBits (A : FullMultiplier.{u} n) :
    (A.splitCircuit).constantBits = A.circuit.constantBits := by
  simp [FullMultiplier.splitCircuit, Circuit.constantBits]

theorem FullMultiplier.splitCircuit_eval (A : FullMultiplier.{u} n)
    {R : Type*} [Ring R] (a b : Fin n → R) :
    A.splitCircuit.eval (Sum.elim a b) =
      A.circuit.eval (fun z => if z.1 then b z.2 else a z.2) := by
  funext j
  unfold FullMultiplier.splitCircuit
  rw [Circuit.eval_comp, Circuit.eval_wire_function]
  have hin :
      (fun z : Bool × Fin n => Sum.elim a b
        (if z.1 then Sum.inr z.2 else Sum.inl z.2)) =
        (fun z => if z.1 then b z.2 else a z.2) := by
    funext z
    cases z with
    | mk bit i => cases bit <;> rfl
  rw [hin]

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

theorem FullMultiplier.splitCircuit_homogeneous (A : FullMultiplier.{u} n) :
    Circuit.RightHomogeneous.{u} A.splitCircuit := by
  intro R _ a r x
  have hscaled :
      vectorPolynomial (2 * n)
          ((A.splitCircuit).eval (Sum.elim a (fun i => r * x i))) =
        vectorPolynomial n a * vectorPolynomial n (fun i => r * x i) := by
    rw [A.splitCircuit_eval a (fun i => r * x i)]
    simpa using
      (A.correct R (fun z : Bool × Fin n => if z.1 then r * x z.2 else a z.2))
  have hunscaled :
      vectorPolynomial (2 * n)
          ((A.splitCircuit).eval (Sum.elim a x)) =
        vectorPolynomial n a * vectorPolynomial n x := by
    rw [A.splitCircuit_eval a x]
    simpa using
      (A.correct R (fun z : Bool × Fin n => if z.1 then x z.2 else a z.2))
  have hpoly :
      vectorPolynomial (2 * n)
          ((A.splitCircuit).eval (Sum.elim a (fun i => r * x i))) =
        Polynomial.C r * vectorPolynomial (2 * n) ((A.splitCircuit).eval (Sum.elim a x)) := by
    rw [hscaled, hunscaled, vectorPolynomial_scale]
    ring
  apply vectorPolynomial_injective (2 * n)
  calc
    vectorPolynomial (2 * n)
        ((A.splitCircuit).eval (Sum.elim a (fun i => r * x i))) =
        Polynomial.C r * vectorPolynomial (2 * n) ((A.splitCircuit).eval (Sum.elim a x)) := hpoly
    _ = vectorPolynomial (2 * n)
        (fun j => r * (A.splitCircuit).eval (Sum.elim a x) j) := by
          rw [vectorPolynomial_scale]

/-- Prepare the actual multiplication-gate operands at the fixed left input. -/
noncomputable def FullMultiplier.parameterPreparation (A : FullMultiplier.{u} n) :
    Circuit (Fin n) (Fin (Fintype.card A.splitCircuit.Tape)) :=
  Circuit.parameterPreparation.{u} A.splitCircuit

/-- The actual linear program on the right input after fixed-factor preparation. -/
noncomputable def FullMultiplier.linearizedProgram (A : FullMultiplier.{u} n) :
    LinearStraightLine.Program (Fintype.card A.splitCircuit.Tape) n (2 * n) :=
  Circuit.linearizedProgram.{u} A.splitCircuit

/-- The transposed linear program, with its fixed-factor preparation included. -/
noncomputable def FullMultiplier.preparedTranspose (A : FullMultiplier.{u} n) :
    Circuit (Fin n ⊕ Fin (2 * n)) (Fin n) :=
  Circuit.preparedTranspose.{u} A.splitCircuit

/-- The prepared forward circuit obtained by compiling the actual linear program. -/
noncomputable def FullMultiplier.preparedForward (A : FullMultiplier.{u} n) :
    Circuit (Fin n ⊕ Fin n) (Fin (2 * n)) :=
  Circuit.preparedForward.{u} A.splitCircuit

theorem FullMultiplier.parameterPreparation_cost (A : FullMultiplier.{u} n) :
    A.parameterPreparation.cost = A.cost := by
  change (Circuit.parameterPreparation.{u} A.splitCircuit).cost = A.cost
  rw [Circuit.parameterPreparation_cost, A.splitCircuit_cost]

theorem FullMultiplier.parameterPreparation_multiplications (A : FullMultiplier.{u} n) :
    A.parameterPreparation.multiplications = A.circuit.multiplications := by
  simpa [FullMultiplier.parameterPreparation, A.splitCircuit_multiplications] using
    (Circuit.parameterPreparation_multiplications A.splitCircuit)

theorem FullMultiplier.parameterPreparation_constantBits (A : FullMultiplier.{u} n) :
    A.parameterPreparation.constantBits = A.circuit.constantBits := by
  simpa [FullMultiplier.parameterPreparation, FullMultiplier.splitCircuit_constantBits] using
    (Circuit.parameterPreparation_constantBits A.splitCircuit)

theorem FullMultiplier.linearizedProgram_multiplications (A : FullMultiplier.{u} n) :
    A.linearizedProgram.compile.multiplications = 2 * A.circuit.multiplications := by
  simpa [FullMultiplier.linearizedProgram, A.splitCircuit_multiplications] using
    (Circuit.linearizedProgram_multiplications A.splitCircuit)

theorem FullMultiplier.linearizedProgram_correct {R : Type u} [CommRing R]
    (A : FullMultiplier.{u} n) (a : Fin n → R) (b : Fin n → R) :
    A.linearizedProgram.eval (A.parameterPreparation.eval a) b =
      A.circuit.eval (fun z => if z.1 then b z.2 else a z.2) := by
  calc
    A.linearizedProgram.eval (A.parameterPreparation.eval a) b =
        A.splitCircuit.eval (Sum.elim a b) :=
      Circuit.linearizedProgram_correct A.splitCircuit A.splitCircuit_homogeneous a b
    _ = A.circuit.eval (fun z => if z.1 then b z.2 else a z.2) :=
      A.splitCircuit_eval a b

theorem FullMultiplier.preparedTranspose_adjoint {R : Type u} [CommRing R]
    (A : FullMultiplier.{u} n) (a b : Fin n → R) (y : Fin (2 * n) → R) :
    A.circuit.eval (fun z => if z.1 then b z.2 else a z.2) ⬝ᵥ y =
      b ⬝ᵥ A.preparedTranspose.eval (Sum.elim a y) := by
  calc
    A.circuit.eval (fun z => if z.1 then b z.2 else a z.2) ⬝ᵥ y =
        A.splitCircuit.eval (Sum.elim a b) ⬝ᵥ y :=
      congrArg (fun f : Fin (2 * n) → R => f ⬝ᵥ y) (A.splitCircuit_eval a b).symm
    _ = b ⬝ᵥ A.preparedTranspose.eval (Sum.elim a y) :=
      Circuit.preparedTranspose_adjoint A.splitCircuit A.splitCircuit_homogeneous a b y

theorem FullMultiplier.preparedForward_correct {R : Type u} [CommRing R]
    (A : FullMultiplier.{u} n) (a b : Fin n → R) :
    A.preparedForward.eval (Sum.elim a b) =
      A.circuit.eval (fun z => if z.1 then b z.2 else a z.2) := by
  calc
    A.preparedForward.eval (Sum.elim a b) = A.splitCircuit.eval (Sum.elim a b) :=
      Circuit.preparedForward_correct A.splitCircuit A.splitCircuit_homogeneous a b
    _ = A.circuit.eval (fun z => if z.1 then b z.2 else a z.2) :=
      A.splitCircuit_eval a b

/-- Retain the multiplication count instead of bounding every gate by a multiplication. -/
theorem FullMultiplier.linearizedProgram_cost_eq (A : FullMultiplier.{u} n) :
    A.linearizedProgram.cost = A.cost + 2 * A.circuit.multiplications := by
  change (Circuit.linearizedProgram.{u} A.splitCircuit).cost = _
  rw [Circuit.linearizedProgram_cost]
  simp only [FullMultiplier.splitCircuit, Circuit.additions, Circuit.negations,
    Circuit.multiplications, Nat.zero_add, FullMultiplier.cost, Circuit.cost]
  omega

theorem FullMultiplier.preparedForward_cost_eq (A : FullMultiplier.{u} n) :
    A.preparedForward.cost = 2 * A.cost + 2 * A.circuit.multiplications := by
  simp only [FullMultiplier.preparedForward, Circuit.preparedForward,
    Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost, Nat.zero_add,
    Nat.add_zero, Circuit.parameterPreparation_cost,
    LinearStraightLine.Program.compile_cost, A.splitCircuit_cost]
  change A.cost + A.linearizedProgram.cost = _
  rw [A.linearizedProgram_cost_eq]
  omega

theorem FullMultiplier.preparedTranspose_cost_refined (A : FullMultiplier.{u} n) :
    A.preparedTranspose.cost ≤ 3 * A.cost + 4 * A.circuit.multiplications + 2 * n := by
  have ht := A.linearizedProgram.transposeCircuit_cost
  rw [A.linearizedProgram_cost_eq] at ht
  simp only [FullMultiplier.preparedTranspose, Circuit.preparedTranspose,
    Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost, Nat.zero_add,
    Nat.add_zero, Circuit.parameterPreparation_cost, A.splitCircuit_cost]
  change A.cost + A.linearizedProgram.transposeCircuit.cost ≤ _
  omega

theorem FullMultiplier.linearizedProgram_cost_le (A : FullMultiplier.{u} n) :
    A.linearizedProgram.cost ≤ 3 * A.cost := by
  change (Circuit.linearizedProgram.{u} A.splitCircuit).cost ≤ 3 * A.cost
  rw [Circuit.linearizedProgram_cost]
  rw [← A.splitCircuit_cost]
  unfold Circuit.cost
  omega

theorem FullMultiplier.preparedTranspose_cost_le (A : FullMultiplier.{u} n) :
    A.preparedTranspose.cost ≤ 7 * A.cost + 2 * n := by
  have h := Circuit.preparedTranspose_cost_le A.splitCircuit
  change (Circuit.preparedTranspose.{u} A.splitCircuit).cost ≤ _ at h
  rw [A.splitCircuit_cost] at h
  simpa [FullMultiplier.preparedTranspose, FullMultiplier.cost] using h

theorem FullMultiplier.preparedForward_cost_le (A : FullMultiplier.{u} n) :
    A.preparedForward.cost ≤ 4 * A.cost := by
  change (Circuit.preparedForward.{u} A.splitCircuit).cost ≤ 4 * A.cost
  have h := Circuit.preparedForward_cost_le A.splitCircuit
  rw [A.splitCircuit_cost] at h
  exact h

theorem FullMultiplier.preparedForward_multiplications (A : FullMultiplier.{u} n) :
    A.preparedForward.multiplications = 3 * A.circuit.multiplications := by
  simpa [FullMultiplier.preparedForward, A.splitCircuit_multiplications] using
    (Circuit.preparedForward_multiplications A.splitCircuit)

theorem FullMultiplier.preparedForward_constantBits (A : FullMultiplier.{u} n) :
    A.preparedForward.constantBits = A.circuit.constantBits := by
  simpa [FullMultiplier.preparedForward, FullMultiplier.splitCircuit_constantBits] using
    (Circuit.preparedForward_constantBits A.splitCircuit)

theorem FullMultiplier.preparedTranspose_multiplications (A : FullMultiplier.{u} n) :
    A.preparedTranspose.multiplications = 3 * A.circuit.multiplications := by
  simpa [FullMultiplier.preparedTranspose, A.splitCircuit_multiplications] using
    (Circuit.preparedTranspose_multiplications A.splitCircuit)

theorem FullMultiplier.preparedTranspose_constantBits (A : FullMultiplier.{u} n) :
    A.preparedTranspose.constantBits = A.circuit.constantBits := by
  simpa [FullMultiplier.preparedTranspose, FullMultiplier.splitCircuit_constantBits] using
    (Circuit.preparedTranspose_constantBits A.splitCircuit)

end DivisionFree.PolynomialArithmetic
