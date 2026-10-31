import DivisionFree.Circuit
import DivisionFree.LinearProgram

/-! Lower elementary linear register programs to the shared arithmetic
circuit syntax. Fixed parameters are explicit inputs, retained between
instructions. The lowering preserves both values and arithmetic gate count. -/

namespace DivisionFree.LinearProgram

variable {n k : ℕ} {R : Type*} [CommRing R]

def Instruction.destination : Instruction n k → Fin n
  | .add dst _ => dst
  | .neg dst => dst
  | .scale dst _ => dst

def Instruction.operation : Instruction n k → Circuit (Fin k ⊕ Fin n) PUnit
  | .add dst src => .comp (.wire (fun b : Bool => Sum.inr (if b then src else dst))) .add
  | .neg dst => .comp (.wire (fun _ => Sum.inr dst)) .neg
  | .scale dst c => .comp (.wire (fun b : Bool =>
      if b then Sum.inr dst else Sum.inl c)) .mul

def Instruction.compile (g : Instruction n k) : Circuit (Fin k ⊕ Fin n) (Fin k ⊕ Fin n) :=
  .comp (.pair (.wire id) g.operation) (.wire (fun s => match s with
    | .inl c => .inl (.inl c)
    | .inr i => if i = g.destination then .inr PUnit.unit else .inl (.inr i)))

@[simp] theorem Instruction.compile_cost (g : Instruction n k) : g.compile.cost = 1 := by
  cases g <;> simp [compile, operation]

theorem Instruction.compile_eval (g : Instruction n k) (p : Fin k → R) (x : Fin n → R) :
    g.compile.eval (Sum.elim p x) = Sum.elim p (g.eval p x) := by
  funext s
  cases g <;> cases s with
  | inl c => simp [compile, operation]
  | inr i =>
    simp only [compile, Circuit.eval_comp, Circuit.eval_wire, destination,
      eval]
    split_ifs <;> simp_all [operation]

def compile : Program n k → Circuit (Fin k ⊕ Fin n) (Fin k ⊕ Fin n)
  | [] => .wire id
  | g :: gs => .comp g.compile (compile gs)

@[simp] theorem compile_cost (P : Program n k) : (compile P).cost = cost P := by
  induction P with
  | nil => rfl
  | cons g gs ih => simp [compile, ih, cost, Nat.add_comm]

theorem compile_eval (P : Program n k) (p : Fin k → R) (x : Fin n → R) :
    (compile P).eval (Sum.elim p x) = Sum.elim p (eval p P x) := by
  induction P generalizing x with
  | nil => rfl
  | cons g gs ih =>
    funext s
    simp only [compile, Circuit.eval_comp]
    rw [Instruction.compile_eval, ih]
    rfl

theorem compiled_transpose_cost (P : Program n k) :
    (compile (transpose P)).cost = (compile P).cost := by simp

theorem compiled_transpose_adjoint (P : Program n k) (p : Fin k → R) (x y : Fin n → R) :
    (fun i => (compile P).eval (Sum.elim p x) (.inr i)) ⬝ᵥ y =
    x ⬝ᵥ (fun i => (compile (transpose P)).eval (Sum.elim p y) (.inr i)) := by
  simp only [compile_eval, Sum.elim_inr]
  exact adjoint p P x y

end DivisionFree.LinearProgram
