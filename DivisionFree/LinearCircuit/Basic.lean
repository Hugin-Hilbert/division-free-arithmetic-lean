import DivisionFree.Circuit

/-! A restricted syntax for circuits that are linear in their value inputs.

The coefficient parameters are supplied separately from the value inputs.
The only operation that combines a parameter with a value is `scale`; there
is no value-by-value multiplication constructor. -/

namespace DivisionFree

open scoped BigOperators

inductive LinearCircuit (K : Type) : Type → Type → Type 1 where
  | wire {I O : Type} (select : O → I) : LinearCircuit K I O
  | zero {I O : Type} : LinearCircuit K I O
  | add : LinearCircuit K Bool PUnit
  | neg : LinearCircuit K PUnit PUnit
  | scale (c : K) : LinearCircuit K PUnit PUnit
  | comp {I J O : Type} [Fintype J]
      (first : LinearCircuit K I J) (second : LinearCircuit K J O) :
      LinearCircuit K I O
  | pair {I O P : Type} (left : LinearCircuit K I O)
      (right : LinearCircuit K I P) : LinearCircuit K I (O ⊕ P)
  | bundle {I J O : Type} [Fintype J]
      (branches : J → LinearCircuit K I O) : LinearCircuit K I (J × O)

namespace LinearCircuit

variable {K I O : Type}

/-- Interpret a linear circuit using a parameter assignment and value inputs. -/
noncomputable def eval {R : Type*} [Ring R] :
    {I O : Type} → LinearCircuit K I O → (K → R) → (I → R) → O → R
  | _, _, .wire select, params, input => fun o => input (select o)
  | _, _, .zero, _, _ => fun _ => 0
  | _, _, .add, _, input => fun _ => input false + input true
  | _, _, .neg, _, input => fun _ => -input PUnit.unit
  | _, _, .scale c, params, input => fun _ => params c * input PUnit.unit
  | _, _, @LinearCircuit.comp _ _ J _ inst first second, params, input => by
      letI := inst
      exact second.eval params (first.eval params input)
  | _, _, .pair left right, params, input =>
      Sum.elim (left.eval params input) (right.eval params input)
  | _, _, @LinearCircuit.bundle _ _ J _ inst branches, params, input => by
      letI := inst
      exact fun p => (branches p.1).eval params input p.2

@[simp] theorem eval_wire {R : Type*} [Ring R]
    (select : O → I) (params : K → R) (input : I → R) (o : O) :
    (wire (K := K) select).eval params input o = input (select o) := rfl

@[simp] theorem eval_zero {R : Type*} [Ring R]
    (params : K → R) (input : I → R) (o : O) :
    (zero : LinearCircuit K I O).eval params input o = 0 := rfl

@[simp] theorem eval_add {R : Type*} [Ring R]
    (params : K → R) (input : Bool → R) (o : PUnit) :
    add.eval params input o = input false + input true := rfl

@[simp] theorem eval_neg {R : Type*} [Ring R]
    (params : K → R) (input : PUnit → R) (o : PUnit) :
    neg.eval params input o = -input PUnit.unit := rfl

@[simp] theorem eval_scale {R : Type*} [Ring R]
    (c : K) (params : K → R) (input : PUnit → R) (o : PUnit) :
    (scale c).eval params input o = params c * input PUnit.unit := rfl

@[simp] theorem eval_comp {R : Type*} [Ring R] {J : Type} [Fintype J]
    (first : LinearCircuit K I J) (second : LinearCircuit K J O)
    (params : K → R) (input : I → R) (o : O) :
    (comp first second).eval params input o =
      second.eval params (first.eval params input) o := rfl

@[simp] theorem eval_pair_inl {R : Type*} [Ring R] {P : Type}
    (left : LinearCircuit K I O) (right : LinearCircuit K I P)
    (params : K → R) (input : I → R) (o : O) :
    (pair left right).eval params input (Sum.inl o) = left.eval params input o := rfl

@[simp] theorem eval_pair_inr {R : Type*} [Ring R] {P : Type}
    (left : LinearCircuit K I O) (right : LinearCircuit K I P)
    (params : K → R) (input : I → R) (o : P) :
    (pair left right).eval params input (Sum.inr o) = right.eval params input o := rfl

@[simp] theorem eval_bundle {R : Type*} [Ring R] {J : Type} [Fintype J]
    (branches : J → LinearCircuit K I O) (params : K → R)
    (input : I → R) (o : J × O) :
    (bundle branches).eval params input o = (branches o.1).eval params input o.2 := rfl

/-- Syntactic number of linear gates: addition, negation, and scalar gates. -/
def cost : {I O : Type} → LinearCircuit K I O → ℕ
  | _, _, .wire _ => 0
  | _, _, .zero => 0
  | _, _, .add => 1
  | _, _, .neg => 1
  | _, _, .scale _ => 1
  | _, _, @LinearCircuit.comp _ _ _ _ _ first second => cost first + cost second
  | _, _, .pair left right => cost left + cost right
  | _, _, @LinearCircuit.bundle _ _ J _ _ branches => ∑ j : J, cost (branches j)

/-- Number of explicit scalar gates, which compile to multiplication gates. -/
def multiplications : {I O : Type} → LinearCircuit K I O → ℕ
  | _, _, .wire _ => 0
  | _, _, .zero => 0
  | _, _, .add => 0
  | _, _, .neg => 0
  | _, _, .scale _ => 1
  | _, _, @LinearCircuit.comp _ _ _ _ _ first second => multiplications first + multiplications second
  | _, _, .pair left right => multiplications left + multiplications right
  | _, _, @LinearCircuit.bundle _ _ J _ _ branches => ∑ j : J, multiplications (branches j)

/-- Compile the parameterized linear syntax into the unrestricted arithmetic
syntax, with coefficient parameters supplied as the left input summand. -/
def compile [Fintype K] : {I O : Type} → LinearCircuit K I O → Circuit (K ⊕ I) O
  | _, _, .wire select => .wire (fun o => Sum.inr (select o))
  | _, _, .zero => .zero
  | _, _, .add => .comp (.wire Sum.inr) .add
  | _, _, .neg => .comp (.wire (fun _ : PUnit => Sum.inr PUnit.unit)) .neg
  | _, _, .scale c => .comp
      (.wire (fun b : Bool => if b then Sum.inr PUnit.unit else Sum.inl c)) .mul
  | _, _, @LinearCircuit.comp _ _ J _ inst first second => by
      letI := inst
      exact .comp (.pair (.wire Sum.inl) (first.compile)) second.compile
  | _, _, .pair left right => .pair left.compile right.compile
  | _, _, @LinearCircuit.bundle _ _ J _ inst branches => by
      letI := inst
      exact .bundle (fun j => (branches j).compile)

theorem compile_eval [Fintype K] {R : Type*} [Ring R]
    (C : LinearCircuit K I O) {params : K → R} {input : I → R} :
    C.compile.eval (Sum.elim params input) = C.eval params input := by
  induction C generalizing params with
  | wire select => rfl
  | zero => rfl
  | add => funext o; simp [compile, eval]
  | neg => funext o; simp [compile, eval]
  | scale c =>
      funext o
      simp [compile, eval]
  | comp first second ihFirst ihSecond =>
      funext o
      simp only [compile, Circuit.eval_comp]
      have hpair : ((Circuit.wire Sum.inl).pair first.compile).eval
          (Sum.elim params input) =
          Sum.elim params (first.compile.eval (Sum.elim params input)) := by
        funext z
        cases z with
        | inl k => simp
        | inr j => rfl
      rw [hpair, ihFirst (params := params) (input := input)]
      rw [eval_comp]
      exact congrFun (ihSecond (params := params)
        (input := first.eval params input)) o
  | pair left right ihLeft ihRight =>
      funext o
      cases o with
      | inl o =>
          simp only [compile, Circuit.eval_pair_inl, eval_pair_inl]
          exact congrFun (ihLeft (params := params) (input := input)) o
      | inr o =>
          simp only [compile, Circuit.eval_pair_inr, eval_pair_inr]
          exact congrFun (ihRight (params := params) (input := input)) o
  | bundle branches ih =>
      funext o
      simp [compile, Circuit.eval_bundle, ih]

theorem compile_cost [Fintype K] {I O : Type}
    (C : LinearCircuit K I O) : C.compile.cost = C.cost := by
  induction C with
  | wire select => rfl
  | zero => rfl
  | add => simp [compile, cost]
  | neg => simp [compile, cost]
  | scale c => simp [compile, cost]
  | comp first second ihFirst ihSecond =>
      simp [compile, cost, ihFirst, ihSecond]
  | pair left right ihLeft ihRight => simp [compile, cost, ihLeft, ihRight]
  | bundle branches ih => simp [compile, cost, ih]

theorem compile_multiplications [Fintype K] {I O : Type}
    (C : LinearCircuit K I O) : C.compile.multiplications = C.multiplications := by
  induction C with
  | wire select => rfl
  | zero => rfl
  | add => simp [compile, multiplications]
  | neg => simp [compile, multiplications]
  | scale c => simp [compile, multiplications]
  | comp first second ihFirst ihSecond =>
      simp [compile, multiplications, ihFirst, ihSecond]
  | pair left right ihLeft ihRight => simp [compile, multiplications, ihLeft, ihRight]
  | bundle branches ih => simp [compile, multiplications, ih]

end LinearCircuit
end DivisionFree
