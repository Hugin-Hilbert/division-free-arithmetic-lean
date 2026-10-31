import DivisionFree.Circuit.BilinearStages

/-! Assemble the prepared parameter and separated linear stages with one
pointwise multiplication layer. -/

namespace DivisionFree.Circuit

open LinearCircuit

universe u

variable {n m r : ℕ}

noncomputable def bilinearParameterInput (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    Circuit (Fin n ⊕ Fin m) (BilinearParameters.{u} C ⊕ (Fin n ⊕ Fin m)) :=
  .pair (.comp .zero (bilinearPreparation.{u} C)) (.wire id)

noncomputable def bilinearBranches (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    Bool → Circuit (BilinearParameters.{u} C ⊕ (Fin n ⊕ Fin m)) C.Tape := by
  classical
  intro b
  cases b with
  | false =>
      exact .comp
        (.wire (Sum.elim Sum.inl (fun x => Sum.inr (Sum.inl x))))
        (bilinearLeft.{u} C).compile
  | true =>
      exact .comp
        (.wire (Sum.elim Sum.inl (fun x => Sum.inr (Sum.inr x))))
        (bilinearRight.{u} C).compile

noncomputable def bilinearStages (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    Circuit (BilinearParameters.{u} C ⊕ (Fin n ⊕ Fin m))
      (BilinearParameters.{u} C ⊕ (Bool × C.Tape)) :=
  .pair (.wire Sum.inl) (.bundle (bilinearBranches.{u} C))

noncomputable def bilinearProductStage (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    Circuit (BilinearParameters.{u} C ⊕ (Bool × C.Tape))
      (BilinearParameters.{u} C ⊕ C.Tape) :=
  .pair (.wire Sum.inl) (.comp (.wire Sum.inr) (pointwiseMultiply (T := C.Tape)))

/-- The concrete circuit computing the output of a bihomogeneous circuit. -/
noncomputable def bilinearCircuit (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    Circuit (Fin n ⊕ Fin m) (Fin r) :=
  .comp (bilinearParameterInput.{u} C)
    (.comp (bilinearStages.{u} C)
      (.comp (bilinearProductStage.{u} C) (bilinearFinish.{u} C).compile))

theorem bilinearCircuit_cost (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearCircuit.{u} C).cost = 4 * C.cost + 10 * C.multiplications := by
  simp [bilinearCircuit, bilinearParameterInput, bilinearStages, bilinearProductStage,
    bilinearBranches, bilinearPreparation_cost, bilinearLeft_cost, bilinearRight_cost,
    bilinearFinish_cost, compile_cost, pointwiseMultiply_cost,
    Circuit.bundle_cost, Circuit.pair_cost, Circuit.comp_cost, tape_card]
  omega

theorem bilinearCircuit_multiplications (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearCircuit.{u} C).multiplications = 9 * C.multiplications := by
  simp [bilinearCircuit, bilinearParameterInput, bilinearStages, bilinearProductStage,
    bilinearBranches, bilinearPreparation_multiplications,
    bilinearLeft_multiplications, bilinearRight_multiplications,
    bilinearFinish_multiplications, compile_multiplications,
    pointwiseMultiply_multiplications, Circuit.bundle_multiplications, tape_card]
  omega

theorem bilinearCircuit_constantBits (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearCircuit.{u} C).constantBits = C.constantBits := by
  simp [bilinearCircuit, bilinearParameterInput, bilinearStages, bilinearProductStage,
    bilinearBranches, bilinearPreparation_constantBits, compile_constantBits,
    Circuit.constantBits]

theorem bilinearCircuit_cost_le (C : Circuit (Fin n ⊕ Fin m) (Fin r)) :
    (bilinearCircuit.{u} C).cost ≤ 14 * C.cost := by
  rw [bilinearCircuit_cost]
  have hm : C.multiplications ≤ C.cost := by
    unfold Circuit.cost
    omega
  nlinarith

theorem bilinearCircuit_eval (C : Circuit (Fin n ⊕ Fin m) (Fin r))
    {R : Type u} [CommRing R] (a : Fin n → R) (b : Fin m → R) :
    (bilinearCircuit.{u} C).eval (Sum.elim a b) =
      (bilinearFinish.{u} C).eval ((bilinearPreparation.{u} C).eval (fun _ => 0))
        (fun t => (bilinearLeft.{u} C).eval ((bilinearPreparation.{u} C).eval (fun _ => 0)) a t *
          (bilinearRight.{u} C).eval ((bilinearPreparation.{u} C).eval (fun _ => 0)) b t) := by
  let params : BilinearParameters.{u} C → R :=
    (bilinearPreparation.{u} C).eval (fun _ => (0 : R))
  have hbranch (q : Bool) (t : C.Tape) :
      (bilinearStages.{u} C).eval
          (Sum.elim params (Sum.elim a b)) (.inr (q, t)) =
        if q then (bilinearRight.{u} C).eval params b t
          else (bilinearLeft.{u} C).eval params a t := by
    have hleftInput :
        (fun o : BilinearParameters.{u} C ⊕ Fin n =>
          Sum.elim params (Sum.elim a b)
            (Sum.elim Sum.inl (fun x => Sum.inr (Sum.inl x)) o)) =
          Sum.elim params a := by
      funext o
      cases o <;> rfl
    have hrightInput :
        (fun o : BilinearParameters.{u} C ⊕ Fin m =>
          Sum.elim params (Sum.elim a b)
            (Sum.elim Sum.inl (fun x => Sum.inr (Sum.inr x)) o)) =
          Sum.elim params b := by
      funext o
      cases o <;> rfl
    cases q with
    | false =>
        rw [bilinearStages, Circuit.eval_pair_inr]
        rw [eval_bundle]
        change (bilinearBranches.{u} C false).eval
          (Sum.elim params (Sum.elim a b)) t = _
        simp only [bilinearBranches, eval_comp_function, eval_wire_function]
        rw [hleftInput, LinearCircuit.compile_eval]
        simp
    | true =>
        rw [bilinearStages, Circuit.eval_pair_inr]
        rw [eval_bundle]
        change (bilinearBranches.{u} C true).eval
          (Sum.elim params (Sum.elim a b)) t = _
        simp only [bilinearBranches, eval_comp_function, eval_wire_function]
        rw [hrightInput, LinearCircuit.compile_eval]
        simp
  have hinput : (bilinearParameterInput.{u} C).eval (Sum.elim a b) =
      Sum.elim params (Sum.elim a b) := by
    simp [bilinearParameterInput, params]
  funext j
  unfold bilinearCircuit
  simp only [Circuit.eval_comp]
  rw [hinput]
  simp only [bilinearProductStage, eval_pair_function, eval_comp_function,
    eval_wire_function]
  rw [LinearCircuit.compile_eval]
  change (bilinearFinish.{u} C).eval params
      (fun t => (pointwiseMultiply (T := C.Tape)).eval
        (fun bt => (bilinearStages.{u} C).eval
          (Sum.elim params (Sum.elim a b)) (.inr bt)) t) j = _
  simp only [pointwiseMultiply_eval]
  simp only [hbranch]
  simp [params]

theorem bilinearCircuit_correct (C : Circuit (Fin n ⊕ Fin m) (Fin r))
    (hC : Bihomogeneous.{u} C) {R : Type u} [CommRing R]
    (a : Fin n → R) (b : Fin m → R) :
    (bilinearCircuit.{u} C).eval (Sum.elim a b) = C.eval (Sum.elim a b) := by
  funext j
  rw [bilinearCircuit_eval, bilinearFinish_eval]
  exact coeff11_of_bihomogeneous C hC a b j

end DivisionFree.Circuit
