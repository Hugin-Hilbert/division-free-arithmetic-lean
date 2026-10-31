import DivisionFree.Circuit
import DivisionFree.Newton

/-!
# Integer leaves and a scalar Newton circuit

Integer leaves are free in the arithmetic-operation model. Their finite signed
binary encoding size is recorded separately. No bound on uniform generation
time is asserted by this definition.
-/

namespace DivisionFree

open scoped BigOperators

def Circuit.constantBits : {I O : Type} → Circuit I O → ℕ
  | _, _, .wire _ => 0
  | _, _, .zero => 0
  | _, _, .integer z => z.natAbs.size + 1
  | _, _, .add => 0
  | _, _, .neg => 0
  | _, _, .mul => 0
  | _, _, @Circuit.comp _ _ _ _ p q => p.constantBits + q.constantBits
  | _, _, .pair p q => p.constantBits + q.constantBits
  | _, _, @Circuit.bundle _ J _ inst ps =>
      letI := inst
      ∑ j : J, (ps j).constantBits

@[simp] theorem Circuit.integer_constantBits {I O : Type} (z : ℤ) :
    (Circuit.integer z : Circuit I O).constantBits = z.natAbs.size + 1 := rfl

@[simp] theorem Circuit.comp_constantBits {I J O : Type} [Fintype J]
    (p : Circuit I J) (q : Circuit J O) :
    (Circuit.comp p q).constantBits = p.constantBits + q.constantBits := rfl

/-- Inputs `false`, `true` are respectively `u`, `v`. -/
def newtonCircuit : Circuit Bool PUnit :=
  .comp (.pair (.wire (fun _ : PUnit => true))
    (Circuit.sum (.integer 2) (Circuit.negative .mul)))
    (.comp (.wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl PUnit.unit)) .mul)

theorem newtonCircuit_correct {R : Type*} [CommRing R] (x : Bool → R) :
    newtonCircuit.eval x PUnit.unit = Newton.step (x false) (x true) := by
  simp [newtonCircuit, Newton.step, sub_eq_add_neg]

theorem newtonCircuit_cost : newtonCircuit.cost = 4 := by
  simp [newtonCircuit]

theorem newtonCircuit_constantBits : newtonCircuit.constantBits = 3 := by
  decide

end DivisionFree
