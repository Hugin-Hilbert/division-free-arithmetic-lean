import DivisionFree.Circuit.Evaluation

/-! Finite labels for stored multiplication operands in a circuit. -/

namespace DivisionFree.Circuit

open scoped BigOperators

/-- A tape label selects one stored operand at a multiplication gate. -/
def Tape : {I O : Type} → Circuit I O → Type
  | _, _, .wire _ => Empty
  | _, _, .zero => Empty
  | _, _, .integer _ => Empty
  | _, _, .add => Empty
  | _, _, .neg => Empty
  | _, _, .mul => Bool
  | _, _, @Circuit.comp _ _ _ _ first second => Sum (Tape first) (Tape second)
  | _, _, .pair left right => Sum (Tape left) (Tape right)
  | _, _, @Circuit.bundle _ _ _ _ branches => Sigma fun j => Tape (branches j)

/-- The tape choices are finite for every finite circuit syntax. -/
noncomputable instance instFintypeTape {I O : Type} (C : Circuit I O) :
    Fintype (Tape C) := by
  classical
  induction C with
  | wire _ => change Fintype Empty; infer_instance
  | zero => change Fintype Empty; infer_instance
  | integer _ => change Fintype Empty; infer_instance
  | add => change Fintype Empty; infer_instance
  | neg => change Fintype Empty; infer_instance
  | mul => change Fintype Bool; infer_instance
  | comp first second ihFirst ihSecond =>
      change Fintype (Sum (Tape first) (Tape second))
      letI := ihFirst
      letI := ihSecond
      infer_instance
  | pair left right ihLeft ihRight =>
      change Fintype (Sum (Tape left) (Tape right))
      letI := ihLeft
      letI := ihRight
      infer_instance
  | bundle branches ih =>
      letI : ∀ j, Fintype (Tape (branches j)) := ih
      change Fintype (Sigma fun j => Tape (branches j))
      infer_instance

/-- The number of tape labels is twice the number of multiplication gates. -/
theorem tape_card {I O : Type} (C : Circuit I O) :
    Fintype.card (Tape C) = 2 * C.multiplications := by
  classical
  induction C with
  | wire _ => simp [Tape, Circuit.multiplications]
  | zero => simp [Tape, Circuit.multiplications]
  | integer _ => simp [Tape, Circuit.multiplications]
  | add => simp [Tape, Circuit.multiplications]
  | neg => simp [Tape, Circuit.multiplications]
  | mul =>
      change Fintype.card Bool = 2
      exact Fintype.card_bool
  | comp first second ihFirst ihSecond =>
      change Fintype.card (Tape first ⊕ Tape second) =
        2 * (first.multiplications + second.multiplications)
      rw [Fintype.card_sum, ihFirst, ihSecond]
      ring
  | pair left right ihLeft ihRight =>
      change Fintype.card (Tape left ⊕ Tape right) =
        2 * (left.multiplications + right.multiplications)
      rw [Fintype.card_sum, ihLeft, ihRight]
      ring
  | bundle branches ih =>
      change Fintype.card (Sigma fun j => Tape (branches j)) =
        2 * (∑ j, (branches j).multiplications)
      rw [Fintype.card_sigma]
      calc
        (∑ j, Fintype.card (Tape (branches j))) =
            ∑ j, 2 * (branches j).multiplications := by
          apply Finset.sum_congr rfl
          intro j hj
          exact ih j
        _ = 2 * ∑ j, (branches j).multiplications := by rw [Finset.mul_sum]

/-- Values attached to gate labels along one tape. This is semantic metadata;
it does not alter the circuit or its gate count. -/
noncomputable def tapeValues {R : Type*} [Ring R] :
    {I O : Type} → (C : Circuit I O) → (I → R) → Tape C → R
  | _, _, .wire _, _, t => Empty.elim t
  | _, _, .zero, _, t => Empty.elim t
  | _, _, .integer _, _, t => Empty.elim t
  | _, _, .add, _, t => Empty.elim t
  | _, _, .neg, _, t => Empty.elim t
  | _, _, .mul, input, b => input b
  | _, _, @Circuit.comp _ _ _ _ first second, input, tape =>
      match tape with
      | Sum.inl firstTape => tapeValues first input firstTape
      | Sum.inr secondTape => tapeValues second (first.eval input) secondTape
  | _, _, .pair left right, input, tape =>
      match tape with
      | Sum.inl leftTape => tapeValues left input leftTape
      | Sum.inr rightTape => tapeValues right input rightTape
  | _, _, @Circuit.bundle _ _ _ _ branches, input, tape =>
      tapeValues (branches tape.1) input tape.2

end DivisionFree.Circuit
