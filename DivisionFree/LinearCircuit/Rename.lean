import DivisionFree.LinearCircuit.Basic

/-! Renaming coefficient parameters and linearity in value inputs. -/

namespace DivisionFree.LinearCircuit

open scoped BigOperators

variable {K L I O : Type}

/-- Rename coefficient parameters without changing the value-input interface. -/
def mapParams (f : K → L) : {I O : Type} → LinearCircuit K I O → LinearCircuit L I O
  | _, _, .wire select => .wire select
  | _, _, .zero => .zero
  | _, _, .add => .add
  | _, _, .neg => .neg
  | _, _, .scale c => .scale (f c)
  | _, _, @LinearCircuit.comp _ _ J _ inst first second => by
      letI := inst
      exact .comp (mapParams f first) (mapParams f second)
  | _, _, .pair left right => .pair (mapParams f left) (mapParams f right)
  | _, _, @LinearCircuit.bundle _ _ J _ inst branches => by
      letI := inst
      exact .bundle (fun j => mapParams f (branches j))

theorem cost_mapParams (f : K → L) (C : LinearCircuit K I O) :
    (mapParams f C).cost = C.cost := by
  induction C with
  | wire select => rfl
  | zero => rfl
  | add => rfl
  | neg => rfl
  | scale c => rfl
  | comp first second ihFirst ihSecond => simp [mapParams, cost, ihFirst, ihSecond]
  | pair left right ihLeft ihRight => simp [mapParams, cost, ihLeft, ihRight]
  | bundle branches ih => simp [mapParams, cost, ih]

theorem multiplications_mapParams (f : K → L) (C : LinearCircuit K I O) :
    (mapParams f C).multiplications = C.multiplications := by
  induction C with
  | wire select => rfl
  | zero => rfl
  | add => rfl
  | neg => rfl
  | scale c => rfl
  | comp first second ihFirst ihSecond => simp [mapParams, multiplications, ihFirst, ihSecond]
  | pair left right ihLeft ihRight => simp [mapParams, multiplications, ihLeft, ihRight]
  | bundle branches ih => simp [mapParams, multiplications, ih]

theorem eval_mapParams {R : Type*} [Ring R] (f : K → L)
    (C : LinearCircuit K I O) (params : L → R) (input : I → R) :
    (mapParams f C).eval params input = C.eval (params ∘ f) input := by
  induction C generalizing params with
  | wire select => rfl
  | zero => rfl
  | add => rfl
  | neg => rfl
  | scale c => rfl
  | comp first second ihFirst ihSecond =>
      funext o
      simp only [mapParams, eval_comp]
      rw [ihFirst, ihSecond]
  | pair left right ihLeft ihRight =>
      funext o
      cases o with
      | inl o => exact congrFun (ihLeft params input) o
      | inr o => exact congrFun (ihRight params input) o
  | bundle branches ih =>
      funext o
      exact congrFun (ih o.1 params input) o.2

/-- The zero value input evaluates to zero under a linear circuit. -/
theorem eval_zero_inputs {R : Type*} [CommRing R]
    (C : LinearCircuit K I O) (params : K → R) :
    C.eval params (fun _ => 0) = fun _ => 0 := by
  induction C with
  | wire select => rfl
  | zero => rfl
  | add => simp [eval]
  | neg => simp [eval]
  | scale c => simp [eval]
  | comp first second ihFirst ihSecond =>
      funext o
      rw [eval_comp, ihFirst, ihSecond]
  | pair left right ihLeft ihRight =>
      funext o
      cases o with
      | inl o => exact congrFun ihLeft o
      | inr o => exact congrFun ihRight o
  | bundle branches ih =>
      funext o
      exact congrFun (ih o.1) o.2

/-- Evaluation preserves sums of value-input families. -/
theorem eval_add_inputs {R : Type*} [CommRing R]
    (C : LinearCircuit K I O) (params : K → R) (x y : I → R) :
    C.eval params (fun i => x i + y i) =
      fun o => C.eval params x o + C.eval params y o := by
  induction C with
  | wire select => rfl
  | zero => simp [eval]
  | add =>
      funext o
      simp [eval]
      ring
  | neg =>
      funext o
      simp [eval]
      ring
  | scale c =>
      funext o
      simp [eval, mul_add]
  | comp first second ihFirst ihSecond =>
      funext o
      rw [eval_comp, ihFirst x y]
      rw [eval_comp, ihSecond (first.eval params x) (first.eval params y)]
      rw [eval_comp]
  | pair left right ihLeft ihRight =>
      funext o
      cases o with
      | inl o => exact congrFun (ihLeft x y) o
      | inr o => exact congrFun (ihRight x y) o
  | bundle branches ih =>
      funext o
      exact congrFun (ih o.1 x y) o.2

/-- Evaluation commutes with uniform scalar multiplication of value inputs. -/
theorem eval_smul_inputs {R : Type*} [CommRing R]
    (C : LinearCircuit K I O) (params : K → R) (a : R) (x : I → R) :
    C.eval params (fun i => a * x i) =
      fun o => a * C.eval params x o := by
  induction C generalizing a with
  | wire select => rfl
  | zero => simp [eval]
  | add =>
      funext o
      simp [eval, mul_add]
  | neg =>
      funext o
      simp [eval]
  | scale c =>
      funext o
      simp [eval]
      ring
  | comp first second ihFirst ihSecond =>
      funext o
      rw [eval_comp, ihFirst a x]
      rw [eval_comp, ihSecond a (first.eval params x)]
  | pair left right ihLeft ihRight =>
      funext o
      cases o with
      | inl o => exact congrFun (ihLeft a x) o
      | inr o => exact congrFun (ihRight a x) o
  | bundle branches ih =>
      funext o
      exact congrFun (ih o.1 a x) o.2

end DivisionFree.LinearCircuit
