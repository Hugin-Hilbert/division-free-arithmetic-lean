import DivisionFree.LinearCircuit.Basic

/-! Change the input wiring of a linear circuit without adding arithmetic. -/

namespace DivisionFree.LinearCircuit

variable {K I J O : Type}

def mapInputs : {I O : Type} → (I → J) → LinearCircuit K I O → LinearCircuit K J O
  | _, _, f, .wire select => .wire (f ∘ select)
  | _, _, _, .zero => .zero
  | _, _, f, .add => .comp (.wire f) .add
  | _, _, f, .neg => .comp (.wire f) .neg
  | _, _, f, .scale c => .comp (.wire f) (.scale c)
  | _, _, f, @LinearCircuit.comp _ _ _ _ inst first second => by
      letI := inst
      exact .comp (mapInputs f first) second
  | _, _, f, .pair left right => .pair (mapInputs f left) (mapInputs f right)
  | _, _, f, @LinearCircuit.bundle _ _ _ _ inst branches => by
      letI := inst
      exact .bundle (fun j => mapInputs f (branches j))

theorem cost_mapInputs (f : I → J) (C : LinearCircuit K I O) :
    (mapInputs f C).cost = C.cost := by
  induction C with
  | wire _ => rfl
  | zero => rfl
  | add => rfl
  | neg => rfl
  | scale _ => rfl
  | comp first second ihFirst _ => simp [mapInputs, cost, ihFirst]
  | pair left right ihLeft ihRight => simp [mapInputs, cost, ihLeft, ihRight]
  | bundle branches ih => simp [mapInputs, cost, ih]

theorem multiplications_mapInputs (f : I → J) (C : LinearCircuit K I O) :
    (mapInputs f C).multiplications = C.multiplications := by
  induction C with
  | wire _ => rfl
  | zero => rfl
  | add => rfl
  | neg => rfl
  | scale _ => rfl
  | comp first second ihFirst _ => simp [mapInputs, multiplications, ihFirst]
  | pair left right ihLeft ihRight => simp [mapInputs, multiplications, ihLeft, ihRight]
  | bundle branches ih => simp [mapInputs, multiplications, ih]

theorem eval_mapInputs {R : Type*} [Ring R] (f : I → J)
    (C : LinearCircuit K I O) (params : K → R) (input : J → R) :
    (mapInputs f C).eval params input = C.eval params (input ∘ f) := by
  induction C with
  | wire _ => rfl
  | zero => rfl
  | add => rfl
  | neg => rfl
  | scale _ => rfl
  | comp first second ihFirst _ =>
      change second.eval params ((mapInputs f first).eval params input) = _
      rw [ihFirst]
      rfl
  | pair left right ihLeft ihRight =>
      funext o
      cases o with
      | inl o => exact congrFun (ihLeft f) o
      | inr o => exact congrFun (ihRight f) o
  | bundle branches ih =>
      funext o
      exact congrFun (ih o.1 f) o.2

end DivisionFree.LinearCircuit
