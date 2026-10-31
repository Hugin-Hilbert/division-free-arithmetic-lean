import DivisionFree.Polynomial.TruncatedMultiplication
import DivisionFree.Constants

/-! Lift a scalar circuit coefficientwise to a truncated polynomial ring. -/

namespace DivisionFree

universe u

open PolynomialArithmetic

namespace Circuit

/-- The coefficientwise lift of a scalar gate to vectors of length `q`. -/
def truncatedLiftAdd (q : ℕ) : Circuit (Bool × Fin q) (PUnit × Fin q) :=
  .comp (.bundle fun i : Fin q =>
      .comp (.wire fun b : Bool => (b, i)) .add)
    (.wire fun (o, i) => (i, o))

/-- Negate each coefficient with one gate per coordinate. -/
def truncatedLiftNeg (q : ℕ) : Circuit (PUnit × Fin q) (PUnit × Fin q) :=
  .comp (.bundle fun i : Fin q =>
      .comp (.wire fun _ : PUnit => (PUnit.unit, i)) .neg)
    (.wire fun (o, i) => (i, o))

/-- Multiply two truncated coefficient vectors by the fast truncated multiplier. -/
noncomputable def truncatedLiftMul (q : ℕ) : Circuit (Bool × Fin q) (PUnit × Fin q) :=
  .comp
    ((PolynomialArithmetic.fastMultiplier.{u} q).circuit)
    (.wire fun (_o, i) => i)

end Circuit

/-- Lift a ring circuit to coefficient vectors for `R[X]/(X^q)`. -/
noncomputable def truncatedLiftAux {I O : Type} (q : ℕ) (fO : Fintype O) : Circuit I O →
    Circuit (I × Fin q) (O × Fin q)
  | .wire select => .wire fun (o, i) => (select o, i)
  | .zero => .zero
  | .integer z =>
      .comp (.pair (.integer z) (.zero : Circuit (I × Fin q) PUnit))
        (.wire fun (_o, i) => if i.val = 0 then Sum.inl PUnit.unit else Sum.inr PUnit.unit)
  | .add => Circuit.truncatedLiftAdd q
  | .neg => Circuit.truncatedLiftNeg q
  | .mul => Circuit.truncatedLiftMul.{u} q
  | @Circuit.comp _ J O inst first second => by
      letI := inst
      exact .comp (truncatedLiftAux q inst first) (truncatedLiftAux q fO second)
  | @Circuit.pair _ A B left right => by
      letI : Fintype (A ⊕ B) := fO
      letI : Fintype A := Fintype.ofInjective (fun a : A => (Sum.inl a : A ⊕ B)) (by
        intro a b h
        exact Sum.inl.inj h)
      letI : Fintype B := Fintype.ofInjective (fun b : B => (Sum.inr b : A ⊕ B)) (by
        intro a b h
        exact Sum.inr.inj h)
      exact .comp (.pair (truncatedLiftAux q inferInstance left)
          (truncatedLiftAux q inferInstance right))
        (.wire fun (o, i) => match o with
          | Sum.inl a => Sum.inl (a, i)
          | Sum.inr b => Sum.inr (b, i))
  | @Circuit.bundle _ J A inst branches => by
      classical
      letI := inst
      letI : Fintype (J × A) := fO
      by_cases h : Nonempty J
      · letI : Fintype A := Fintype.ofInjective (fun o => (Classical.choice h, o))
          (by intro a b e; exact (Prod.mk.inj e).2)
        exact .comp (.bundle fun j => truncatedLiftAux q inferInstance (branches j))
          (.wire fun ((j, o), i) => (j, (o, i)))
      · exact .zero

/-- Lift a ring circuit to coefficient vectors for `R[X]/(X^q)`. -/
noncomputable def truncatedLift {I O : Type} [Fintype O] (q : ℕ) (C : Circuit I O) :
    Circuit (I × Fin q) (O × Fin q) :=
  truncatedLiftAux.{u} q ‹Fintype O› C

namespace Circuit

variable {I O : Type}

@[simp] theorem truncatedLift_wire (q : ℕ) [Fintype O] (select : O → I) :
    truncatedLift q (wire select) = wire (fun (o, i) => (select o, i)) := by
  simp [truncatedLift, truncatedLiftAux]

@[simp] theorem truncatedLift_zero (q : ℕ) [Fintype O] :
    truncatedLift q (zero : Circuit I O) = zero := by simp [truncatedLift, truncatedLiftAux]

@[simp] theorem truncatedLift_integer (q : ℕ) [Fintype O] (z : ℤ) :
    truncatedLift q (integer z : Circuit I O) =
      comp (pair (integer z) (zero : Circuit (I × Fin q) PUnit))
        (wire fun (_o, i) => if i.val = 0 then Sum.inl PUnit.unit else Sum.inr PUnit.unit) := by
  simp [truncatedLift, truncatedLiftAux]

end Circuit

namespace Circuit

variable {I O : Type}

theorem truncatedLift_add_cost (q : ℕ) :
    (Circuit.truncatedLiftAdd q).cost = q := by
  simp [truncatedLiftAdd, Circuit.bundle_cost]

theorem truncatedLift_neg_cost (q : ℕ) :
    (Circuit.truncatedLiftNeg q).cost = q := by
  simp [truncatedLiftNeg, Circuit.bundle_cost]

theorem truncatedLift_mul_cost (q : ℕ) :
    (Circuit.truncatedLiftMul.{u} q).cost =
      (PolynomialArithmetic.fastMultiplier.{u} q).cost := by
  rfl

end Circuit

end DivisionFree
