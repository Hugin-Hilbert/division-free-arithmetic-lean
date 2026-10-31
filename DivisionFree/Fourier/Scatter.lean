import DivisionFree.Polynomial.Schoolbook
import DivisionFree.Constants

/-!
# Finite scatter-add circuits

A scatter circuit routes each source value to its selected target and adds
colliding values using explicit ring addition gates.
-/

namespace DivisionFree.Fourier

open DivisionFree
open scoped BigOperators

variable {I O : Type} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

private noncomputable def scatterFiber (f : I → O) (o : O) : Circuit I PUnit :=
  Circuit.sumList (((Finset.univ.filter fun i => f i = o).toList).map
    fun i => Circuit.wire (fun _ => i))

/-- Send each source coordinate to its target, adding all values that collide. -/
noncomputable def scatter (f : I → O) : Circuit I O :=
  .comp (.bundle fun o => scatterFiber f o)
    (.wire fun o : O => (o, PUnit.unit))

omit [DecidableEq I] in
@[simp] theorem scatter_eval {R : Type*} [Ring R]
    (f : I → O) (x : I → R) (o : O) :
    (scatter f).eval x o = ∑ i : I, if f i = o then x i else 0 := by
  classical
  simp [scatter, scatterFiber, Circuit.sumList_eval, List.map_map,
    Function.comp_def, Finset.sum_filter]

omit [DecidableEq I] [Fintype O] in
private theorem scatterFiber_cost (f : I → O) (o : O) :
    (scatterFiber f o).cost = (Finset.univ.filter fun i => f i = o).card := by
  simp [scatterFiber, Circuit.sumList_cost, List.map_map, Function.comp_def]

omit [DecidableEq I] in
theorem scatter_cost (f : I → O) : (scatter f).cost = Fintype.card I := by
  classical
  simp only [scatter, Circuit.comp_cost, Circuit.bundle_cost, Circuit.wire_cost,
    scatterFiber_cost]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

private theorem sumList_wire_multiplications {J I : Type} (is : List J)
    (select : J → I) :
    (Circuit.sumList (is.map fun j => Circuit.wire (fun _ : PUnit => select j))).multiplications = 0 := by
  induction is with
  | nil => rfl
  | cons j js ih => simp [Circuit.sumList, ih]

private theorem sumList_wire_constantBits {J I : Type} (is : List J)
    (select : J → I) :
    (Circuit.sumList (is.map fun j => Circuit.wire (fun _ : PUnit => select j))).constantBits = 0 := by
  induction is with
  | nil => rfl
  | cons j js ih => simp [Circuit.sumList, ih, Circuit.sum, Circuit.constantBits]

omit [DecidableEq I] in
theorem scatter_multiplications (f : I → O) :
    (scatter f).multiplications = 0 := by
  classical
  simp [scatter, scatterFiber, sumList_wire_multiplications, Circuit.multiplications]

omit [DecidableEq I] in
theorem scatter_constantBits (f : I → O) :
    (scatter f).constantBits = 0 := by
  classical
  simp [scatter, scatterFiber, sumList_wire_constantBits, Circuit.constantBits]

omit [DecidableEq I] in
theorem scatter_weighted_sum {R : Type*} [CommRing R]
    (f : I → O) (x : I → R) (w : O → R) :
    (∑ o : O, (scatter f).eval x o * w o) =
      ∑ i : I, x i * w (f i) := by
  classical
  simp_rw [scatter_eval, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

end DivisionFree.Fourier
