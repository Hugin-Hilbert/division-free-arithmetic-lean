import DivisionFree.Circuit.Tape
import DivisionFree.Circuit.PartialWire

/-! Evaluate a circuit and retain the two operands of every multiplication
gate. Composition evaluates its first stage once and shares both its outputs
and stored operands with the continuation. -/

namespace DivisionFree.Circuit

universe u

variable {I J O P : Type}

/-- An actual circuit computes the original outputs and the complete operand
tape, with exactly the original arithmetic and integer-constant resources. -/
structure Prepared (C : Circuit I O) where
  circuit : Circuit I (O ⊕ C.Tape)
  cost_eq : circuit.cost = C.cost
  multiplications_eq : circuit.multiplications = C.multiplications
  constantBits_eq : circuit.constantBits = C.constantBits
  correct : ∀ (R : Type u) [Ring R] (x : I → R),
    circuit.eval x = Sum.elim (C.eval x) (C.tapeValues x)

private def emptyPrepared (C : Circuit I O) [IsEmpty C.Tape] : Prepared.{u} C where
  circuit := .pair C .zero
  cost_eq := by simp
  multiplications_eq := by simp
  constantBits_eq := by simp [constantBits]
  correct R _ x := by
    funext o
    cases o with
    | inl o => rfl
    | inr t => exact isEmptyElim t

private def noTapePrepared (C : Circuit I O) (h : C.Tape = Empty) : Prepared.{u} C := by
  letI : IsEmpty C.Tape := h.symm ▸ (inferInstance : IsEmpty Empty)
  exact emptyPrepared C

private def mulPrepared : Prepared.{u} Circuit.mul where
  circuit := .pair .mul (.wire id)
  cost_eq := rfl
  multiplications_eq := rfl
  constantBits_eq := rfl
  correct _ _ _ := rfl

private noncomputable def compPrepared [Fintype J] [Fintype O]
    {F : Circuit I J} {G : Circuit J O}
    (A : Prepared.{u} F) (B : Prepared.{u} G) : Prepared.{u} (.comp F G) where
  circuit := .comp A.circuit
    (.comp (.pair (.comp (.wire Sum.inl) B.circuit) (.wire Sum.inr))
      (.wire fun o => match o with
        | .inl o => .inl (.inl o)
        | .inr (.inl t) => .inr t
        | .inr (.inr t) => .inl (.inr t)))
  cost_eq := by simp [A.cost_eq, B.cost_eq]
  multiplications_eq := by simp [A.multiplications_eq, B.multiplications_eq]
  constantBits_eq := by simp [constantBits, A.constantBits_eq, B.constantBits_eq]
  correct R _ x := by
    simp only [eval_comp_function, eval_pair_function, eval_wire_function, A.correct, B.correct]
    funext o
    cases o with
    | inl o => simp [tapeValues]
    | inr t => cases t <;> simp [tapeValues]

private noncomputable def pairPrepared [Fintype O] [Fintype P]
    {F : Circuit I O} {G : Circuit I P}
    (A : Prepared.{u} F) (B : Prepared.{u} G) : Prepared.{u} (.pair F G) where
  circuit := .comp (.pair A.circuit B.circuit)
    (.wire fun o => match o with
      | .inl (.inl o) => .inl (.inl o)
      | .inl (.inr o) => .inr (.inl o)
      | .inr (.inl t) => .inl (.inr t)
      | .inr (.inr t) => .inr (.inr t))
  cost_eq := by simp [A.cost_eq, B.cost_eq]
  multiplications_eq := by simp [A.multiplications_eq, B.multiplications_eq]
  constantBits_eq := by simp [constantBits, A.constantBits_eq, B.constantBits_eq]
  correct R _ x := by
    simp only [eval_comp_function, eval_pair_function, eval_wire_function, A.correct, B.correct]
    funext o
    cases o with
    | inl o => cases o <;> rfl
    | inr t => cases t <;> rfl

private def branchSelect [DecidableEq J] (C : J → Circuit I O) (j : J) :
    O ⊕ (Sigma fun l => (C l).Tape) → Option (O ⊕ (C j).Tape)
  | .inl o => some (.inl o)
  | .inr ⟨l, t⟩ => if h : l = j then some (.inr (h ▸ t)) else none

private noncomputable def bundlePrepared [Fintype J] [Fintype (J × O)]
    (C : J → Circuit I O) (A : ∀ j, Prepared.{u} (C j)) : Prepared.{u} (.bundle C) := by
  classical
  let T := Sigma fun j => (C j).Tape
  letI : Fintype (J × (O ⊕ T)) :=
    Fintype.ofEquiv ((J × O) ⊕ (J × T)) (Equiv.prodSumDistrib J O T).symm
  let branch (j : J) : Circuit I (O ⊕ T) := by
    letI : Fintype O := Fintype.ofInjective (fun o : O => (j, o))
      (by intro a b h; exact congrArg Prod.snd h)
    exact .comp (A j).circuit (partialWire (branchSelect C j))
  refine
    { circuit := .comp (.bundle branch)
        (.wire fun o => match o with
          | .inl (j, o) => (j, .inl o)
          | .inr t => (t.1, .inr t))
      cost_eq := ?_
      multiplications_eq := ?_
      constantBits_eq := ?_
      correct := ?_ }
  · simp [branch, (A _).cost_eq]
  · simp [branch, (A _).multiplications_eq]
  · simp [branch, constantBits, (A _).constantBits_eq]
  · intro R _ x
    have hleft (j : J) (o : O) : (branch j).eval x (.inl o) = (C j).eval x o := by
      simp only [branch, eval_comp, partialWire_eval, branchSelect, Option.elim_some]
      exact congrFun ((A j).correct R x) (.inl o)
    have hright (j : J) (t : (C j).Tape) :
        (branch j).eval x (.inr ⟨j, t⟩) = (C j).tapeValues x t := by
      simp only [branch, eval_comp, partialWire_eval, branchSelect]
      exact congrFun ((A j).correct R x) (.inr t)
    funext o
    cases o with
    | inl o =>
        rcases o with ⟨j, o⟩
        simpa only [eval_comp, eval_wire, eval_bundle, Sum.elim_inl] using hleft j o
    | inr t =>
        rcases t with ⟨j, t⟩
        simpa only [eval_comp, eval_wire, eval_bundle, Sum.elim_inr, tapeValues] using hright j t

/-- Store multiplication operands without rerunning any subcircuit. -/
noncomputable def prepare (C : Circuit I O) : [Fintype O] → Prepared.{u} C := by
  induction C with
  | wire select => intro _; exact noTapePrepared (.wire select) rfl
  | zero => intro _; exact noTapePrepared .zero rfl
  | integer z => intro _; exact noTapePrepared (.integer z) rfl
  | add => intro _; exact noTapePrepared .add rfl
  | neg => intro _; exact noTapePrepared .neg rfl
  | mul => intro _; exact mulPrepared
  | comp first second ihFirst ihSecond =>
      intro _
      exact compPrepared ihFirst ihSecond
  | @pair I O P first second ihFirst ihSecond =>
      intro _
      letI : Fintype O := Fintype.ofInjective (Sum.inl : O → O ⊕ P) Sum.inl_injective
      letI : Fintype P := Fintype.ofInjective (Sum.inr : P → O ⊕ P) Sum.inr_injective
      exact pairPrepared ihFirst ihSecond
  | @bundle I J O inst branches ih =>
      intro _
      exact bundlePrepared branches (fun j => by
        letI : Fintype O := Fintype.ofInjective (fun o : O => (j, o))
          (by intro a b h; exact congrArg Prod.snd h)
        exact ih j)

end DivisionFree.Circuit
