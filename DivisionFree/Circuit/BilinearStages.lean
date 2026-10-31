import DivisionFree.Circuit.Prepare
import DivisionFree.Circuit.MixedLinearization
import DivisionFree.Circuit.MixedFirstOrder
import DivisionFree.Circuit.Bihomogeneous
import DivisionFree.Circuit.Pointwise
import DivisionFree.LinearCircuit.Constants

/-! Concrete separated linear stages for the bilinear part of any circuit.
All scalar parameters are computed once by a preparation circuit at zero. -/

namespace DivisionFree.Circuit

open LinearCircuit PolynomialArithmetic

universe u

variable {n m r : ℕ}

/-- Parameters for first-order operand extraction and final mixed propagation. -/
abbrev BilinearParameters (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :=
  (prepare.{u} C).circuit.Tape ⊕ C.Tape

noncomputable def bilinearPreparation (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    Circuit PUnit (BilinearParameters.{u} C) :=
  .comp .zero (.comp (prepare.{u} (prepare.{u} C).circuit).circuit
    (.wire (Sum.elim Sum.inr (fun t => Sum.inl (Sum.inr t)))))

theorem bilinearPreparation_cost (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearPreparation.{u} C).cost = C.cost := by
  simp only [bilinearPreparation, comp_cost, zero_cost, wire_cost, Nat.zero_add,
    Nat.add_zero, (prepare.{u} (prepare.{u} C).circuit).cost_eq, (prepare.{u} C).cost_eq]

theorem bilinearPreparation_multiplications (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearPreparation.{u} C).multiplications = C.multiplications := by
  simp only [bilinearPreparation, comp_multiplications, zero_multiplications,
    wire_multiplications, Nat.zero_add, Nat.add_zero,
    (prepare.{u} (prepare.{u} C).circuit).multiplications_eq,
    (prepare.{u} C).multiplications_eq]

theorem bilinearPreparation_constantBits (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearPreparation.{u} C).constantBits = C.constantBits := by
  simp only [bilinearPreparation, comp_constantBits, constantBits, Nat.zero_add,
    Nat.add_zero, (prepare.{u} (prepare.{u} C).circuit).constantBits_eq,
    (prepare.{u} C).constantBits_eq]

theorem bilinearPreparation_eval (C : Circuit (Fin n ⊕ Fin m) (Fin r))
    {R : Type u} [CommRing R] (input : PUnit → R) :
    (bilinearPreparation.{u} C).eval input =
      Sum.elim ((prepare.{u} C).circuit.tapeValues (fun _ => 0))
        (C.tapeValues (fun _ => 0)) := by
  simp only [bilinearPreparation, eval_comp_function, eval_zero_function,
    eval_wire_function]
  rw [(prepare.{u} (prepare.{u} C).circuit).correct R (fun _ => 0)]
  funext z
  cases z with
  | inl t => rfl
  | inr t => exact congrFun ((prepare.{u} C).correct R (fun _ => 0)) (Sum.inr t)

/-- The left stage uses only the left vector and fixed prepared scalars. -/
noncomputable def bilinearLeft (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    LinearCircuit (BilinearParameters.{u} C) (Fin n) C.Tape :=
  .comp (.pair (.wire id) .zero)
    (.comp (mapParams Sum.inl (prepare.{u} C).circuit.differential) (.wire Sum.inr))

/-- The right stage uses only the right vector; operand labels are swapped
so that corresponding output coordinates are precisely the cross-products. -/
noncomputable def bilinearRight (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    LinearCircuit (BilinearParameters.{u} C) (Fin m) C.Tape :=
  .comp (.pair .zero (.wire id))
    (.comp (mapParams Sum.inl (prepare.{u} C).circuit.differential)
      (.wire (fun t => Sum.inr (C.tapeSwap t))))

/-- Final linear propagation after the single layer of pairwise products. -/
noncomputable def bilinearFinish (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    LinearCircuit (BilinearParameters.{u} C) C.Tape (Fin r) :=
  .comp (.pair .zero (.wire id)) (mapParams Sum.inr C.mixedLinear)

theorem bilinearLeft_cost (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearLeft.{u} C).cost = C.cost + 2 * C.multiplications := by
  simp only [bilinearLeft, LinearCircuit.cost, cost_mapParams,
    differential_cost, Nat.zero_add, Nat.add_zero]
  have hc := (prepare.{u} C).cost_eq
  have hm := (prepare.{u} C).multiplications_eq
  unfold cost at hc ⊢
  omega

theorem bilinearRight_cost (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearRight.{u} C).cost = C.cost + 2 * C.multiplications := by
  change (bilinearLeft.{u} C).cost = _
  exact bilinearLeft_cost C

theorem bilinearFinish_cost (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearFinish.{u} C).cost = C.cost + 4 * C.multiplications := by
  simp only [bilinearFinish, LinearCircuit.cost, cost_mapParams,
    mixedLinear_cost, Nat.zero_add]
  unfold cost
  omega

theorem bilinearLeft_multiplications (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearLeft.{u} C).multiplications = 2 * C.multiplications := by
  simp only [bilinearLeft, LinearCircuit.multiplications, multiplications_mapParams,
    differential_multiplications, Nat.zero_add, Nat.add_zero,
    (prepare.{u} C).multiplications_eq]

theorem bilinearRight_multiplications (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearRight.{u} C).multiplications = 2 * C.multiplications := by
  change (bilinearLeft.{u} C).multiplications = _
  exact bilinearLeft_multiplications C

theorem bilinearFinish_multiplications (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearFinish.{u} C).multiplications = 2 * C.multiplications := by
  simp only [bilinearFinish, LinearCircuit.multiplications, multiplications_mapParams,
    mixedLinear_multiplications, Nat.zero_add]

theorem bilinearLeft_eval (C : Circuit (Fin n ⊕ Fin m) (Fin r))
    {R : Type u} [CommRing R] (a : Fin n → R) (b : Fin m → R) (t : C.Tape) :
    (bilinearLeft.{u} C).eval ((bilinearPreparation.{u} C).eval (fun _ => 0)) a t =
      coeff10 (C.tapeValues (bilinearInput a b) t) := by
  have hd := differential_coeff10 (prepare.{u} C).circuit (bilinearInput a b) (Sum.inr t)
  rw [bilinearInput_coeff00, bilinearInput_coeff10] at hd
  have hp := congrFun ((prepare.{u} C).correct (Polynomial (Polynomial R))
    (bilinearInput a b)) (Sum.inr t)
  rw [hp] at hd
  rw [bilinearPreparation_eval]
  change (mapParams Sum.inl (prepare.{u} C).circuit.differential).eval
    (Sum.elim ((prepare.{u} C).circuit.tapeValues (fun _ => 0)) (C.tapeValues (fun _ => 0)))
    (Sum.elim a (fun _ => 0)) (Sum.inr t) = _
  rw [eval_mapParams]
  exact hd.symm

theorem bilinearRight_eval (C : Circuit (Fin n ⊕ Fin m) (Fin r))
    {R : Type u} [CommRing R] (a : Fin n → R) (b : Fin m → R) (t : C.Tape) :
    (bilinearRight.{u} C).eval ((bilinearPreparation.{u} C).eval (fun _ => 0)) b t =
      coeff01 (C.tapeValues (bilinearInput a b) (C.tapeSwap t)) := by
  have hd := differential_coeff01 (prepare.{u} C).circuit (bilinearInput a b)
    (Sum.inr (C.tapeSwap t))
  rw [bilinearInput_coeff00, bilinearInput_coeff01] at hd
  have hp := congrFun ((prepare.{u} C).correct (Polynomial (Polynomial R))
    (bilinearInput a b)) (Sum.inr (C.tapeSwap t))
  rw [hp] at hd
  rw [bilinearPreparation_eval]
  change (mapParams Sum.inl (prepare.{u} C).circuit.differential).eval
    (Sum.elim ((prepare.{u} C).circuit.tapeValues (fun _ => 0)) (C.tapeValues (fun _ => 0)))
    (Sum.elim (fun _ => 0) b) (Sum.inr (C.tapeSwap t)) = _
  rw [eval_mapParams]
  exact hd.symm

theorem bilinearFinish_eval (C : Circuit (Fin n ⊕ Fin m) (Fin r))
    {R : Type u} [CommRing R] (a : Fin n → R) (b : Fin m → R) (j : Fin r) :
    (bilinearFinish.{u} C).eval ((bilinearPreparation.{u} C).eval (fun _ => 0))
      (fun t => (bilinearLeft.{u} C).eval ((bilinearPreparation.{u} C).eval (fun _ => 0)) a t *
        (bilinearRight.{u} C).eval ((bilinearPreparation.{u} C).eval (fun _ => 0)) b t) j =
      coeff11 (C.eval (bilinearInput a b) j) := by
  simp_rw [bilinearLeft_eval C a b, bilinearRight_eval C a b]
  have hd := mixedLinear_eval_coeff11 C (bilinearInput a b) j
  rw [bilinearInput_coeff00, bilinearInput_coeff11] at hd
  rw [bilinearPreparation_eval]
  change (mapParams Sum.inr C.mixedLinear).eval
    (Sum.elim ((prepare.{u} C).circuit.tapeValues (fun _ => 0)) (C.tapeValues (fun _ => 0)))
    (Sum.elim (fun _ => 0) (C.crossValues (bilinearInput a b))) j = _
  rw [eval_mapParams]
  exact hd.symm

end DivisionFree.Circuit
