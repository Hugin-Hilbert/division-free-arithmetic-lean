import DivisionFree.Circuit
import DivisionFree.Constants

/-!
# Coefficient-array circuits for cyclic arithmetic

These circuits use only wires and scalar addition or negation gates. They are
independent of Fourier roots and work over every ring.
-/

namespace DivisionFree.Fourier

open DivisionFree

variable (m : ℕ) [NeZero m]

/-- Shift a coefficient array cyclically by `e`. -/
def cyclicShift (e : ZMod m) : Circuit (ZMod m) (ZMod m) :=
  .wire (fun j => j - e)

omit [NeZero m] in
@[simp] theorem cyclicShift_eval (e : ZMod m) {R : Type*} [Ring R] (x : ZMod m → R) (j : ZMod m) :
    (cyclicShift m e).eval x j = x (j - e) := rfl

omit [NeZero m] in
@[simp] theorem cyclicShift_cost (e : ZMod m) : (cyclicShift m e).cost = 0 := rfl

omit [NeZero m] in
@[simp] theorem cyclicShift_constantBits (e : ZMod m) :
    (cyclicShift m e).constantBits = 0 := rfl

/-- Add the two coefficient arrays in a pair of cyclic arrays. -/
def cyclicAdd : Circuit (Bool × ZMod m) (ZMod m) :=
  .comp
    (.bundle (fun j : ZMod m =>
      .comp (.wire (fun b : Bool => (b, j))) .add))
    (.wire (fun j : ZMod m => (j, PUnit.unit)))

@[simp] theorem cyclicAdd_eval {R : Type*} [Ring R]
    (x : Bool × ZMod m → R) (j : ZMod m) :
    (cyclicAdd m).eval x j = x (false, j) + x (true, j) := by
  simp [cyclicAdd]

theorem cyclicAdd_cost : (cyclicAdd m).cost = m := by
  classical
  simp [cyclicAdd]

theorem cyclicAdd_constantBits : (cyclicAdd m).constantBits = 0 := by
  classical
  simp [cyclicAdd, Circuit.constantBits]

/-- Negate every coefficient of a cyclic array. -/
def cyclicNeg : Circuit (ZMod m) (ZMod m) :=
  .comp
    (.bundle (fun j : ZMod m =>
      .comp (.wire (fun _ : PUnit => j)) .neg))
    (.wire (fun j : ZMod m => (j, PUnit.unit)))

@[simp] theorem cyclicNeg_eval {R : Type*} [Ring R]
    (x : ZMod m → R) (j : ZMod m) :
    (cyclicNeg m).eval x j = -x j := by
  simp [cyclicNeg]

theorem cyclicNeg_cost : (cyclicNeg m).cost = m := by
  classical
  simp [cyclicNeg]

theorem cyclicNeg_constantBits : (cyclicNeg m).constantBits = 0 := by
  classical
  simp [cyclicNeg, Circuit.constantBits]

end DivisionFree.Fourier
