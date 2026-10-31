import DivisionFree.Circuit

/-! Function-level evaluation identities for circuit constructors. -/

namespace DivisionFree.Circuit

variable {R : Type*} [Ring R]

@[simp] theorem eval_wire_function {I O : Type} (select : O → I)
    (input : I → R) :
    (Circuit.wire select).eval input = fun o => input (select o) := rfl

@[simp] theorem eval_zero_function {I O : Type} (input : I → R) :
    (Circuit.zero : Circuit I O).eval input = fun _ => 0 := rfl

@[simp] theorem eval_comp_function {I J O : Type} [Fintype J]
    (first : Circuit I J) (second : Circuit J O) (input : I → R) :
    (Circuit.comp first second).eval input = second.eval (first.eval input) := by
  funext o
  exact eval_comp first second input o

@[simp] theorem eval_pair_function {I O P : Type}
    (left : Circuit I O) (right : Circuit I P) (input : I → R) :
    (Circuit.pair left right).eval input =
      Sum.elim (left.eval input) (right.eval input) := rfl

@[simp] theorem eval_bundle_function {I J O : Type} [Fintype J]
    (branches : J → Circuit I O) (input : I → R) :
    (Circuit.bundle branches).eval input = fun p =>
      (branches p.1).eval input p.2 := by
  funext p
  exact eval_bundle branches input p

end DivisionFree.Circuit
