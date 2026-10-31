import DivisionFree.Circuit.Tape

/-! Swap the two operand labels at each multiplication gate in a tape. -/

namespace DivisionFree.Circuit

def tapeSwap : {I O : Type} → (C : Circuit I O) → Tape C → Tape C
  | _, _, .wire _, t => Empty.elim t
  | _, _, .zero, t => Empty.elim t
  | _, _, .integer _, t => Empty.elim t
  | _, _, .add, t => Empty.elim t
  | _, _, .neg, t => Empty.elim t
  | _, _, .mul, b => !b
  | _, _, @Circuit.comp _ _ _ _ first second, tape =>
      match tape with
      | Sum.inl t => Sum.inl (tapeSwap first t)
      | Sum.inr t => Sum.inr (tapeSwap second t)
  | _, _, .pair left right, tape =>
      match tape with
      | Sum.inl t => Sum.inl (tapeSwap left t)
      | Sum.inr t => Sum.inr (tapeSwap right t)
  | _, _, @Circuit.bundle _ J _ inst branches, tape => by
      letI := inst
      exact match tape with
        | Sigma.mk j t => Sigma.mk j (tapeSwap (branches j) t)

theorem tapeSwap_involutive {I O : Type} (C : Circuit I O) (t : Tape C) :
    tapeSwap C (tapeSwap C t) = t := by
  induction C with
  | wire _ => exact Empty.elim t
  | zero => exact Empty.elim t
  | integer _ => exact Empty.elim t
  | add => exact Empty.elim t
  | neg => exact Empty.elim t
  | mul => cases t <;> simp [tapeSwap]
  | comp first second ihFirst ihSecond =>
      cases t with
      | inl t => exact congrArg Sum.inl (ihFirst t)
      | inr t => exact congrArg Sum.inr (ihSecond t)
  | pair left right ihLeft ihRight =>
      cases t with
      | inl t => exact congrArg Sum.inl (ihLeft t)
      | inr t => exact congrArg Sum.inr (ihRight t)
  | bundle branches ih =>
      cases t with
      | mk j t => exact congrArg (Sigma.mk j) (ih j t)

end DivisionFree.Circuit
