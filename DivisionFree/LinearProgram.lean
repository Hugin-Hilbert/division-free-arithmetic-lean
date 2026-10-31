import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# Transposition for elementary register programs

Parameters are fixed scalars, independent of the input vector. Each instruction
updates one register with one addition, negation, or multiplication. Reversing
instruction order and transposing each instruction computes the adjoint at
exactly the same gate cost. This is a square in-place model; compiling arbitrary
rectangular straight-line programs, fanout, and boundary initialization is a
separate task.
-/

namespace DivisionFree.LinearProgram

open scoped BigOperators

inductive Instruction (registers parameters : ℕ) where
  | add (dst src : Fin registers)
  | neg (dst : Fin registers)
  | scale (dst : Fin registers) (parameter : Fin parameters)
  deriving DecidableEq

variable {n k : ℕ} {R : Type*} [CommRing R]

def Instruction.eval (p : Fin k → R) : Instruction n k → (Fin n → R) → Fin n → R
  | .add dst src, x => Function.update x dst (x dst + x src)
  | .neg dst, x => Function.update x dst (-x dst)
  | .scale dst c, x => Function.update x dst (p c * x dst)

def Instruction.transpose : Instruction n k → Instruction n k
  | .add dst src => .add src dst
  | .neg dst => .neg dst
  | .scale dst c => .scale dst c

@[simp] theorem Instruction.transpose_transpose (g : Instruction n k) :
    g.transpose.transpose = g := by cases g <;> rfl

private theorem dot_update (x y : Fin n → R) (i : Fin n) (v : R) :
    (Function.update x i v) ⬝ᵥ y = x ⬝ᵥ y + (v - x i) * y i := by
  have he : Function.update x i v = x + Pi.single i (v - x i) := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  rw [he, add_dotProduct, single_dotProduct]

private theorem dot_update_right (x y : Fin n → R) (i : Fin n) (v : R) :
    x ⬝ᵥ (Function.update y i v) = x ⬝ᵥ y + x i * (v - y i) := by
  rw [dotProduct_comm x, dot_update, dotProduct_comm y x]
  ring

theorem Instruction.adjoint (p : Fin k → R) (g : Instruction n k)
    (x y : Fin n → R) : g.eval p x ⬝ᵥ y = x ⬝ᵥ g.transpose.eval p y := by
  cases g with
  | add dst src =>
    simp only [eval, transpose]
    rw [dot_update, dot_update_right]
    ring
  | neg dst =>
    simp only [eval, transpose]
    rw [dot_update, dot_update_right]
    ring
  | scale dst c =>
    simp only [eval, transpose]
    rw [dot_update, dot_update_right]
    ring

abbrev Program (n k : ℕ) := List (Instruction n k)

def eval (p : Fin k → R) : Program n k → (Fin n → R) → Fin n → R
  | [], x => x
  | g :: gs, x => eval p gs (g.eval p x)

def transpose (P : Program n k) : Program n k := P.reverse.map Instruction.transpose

/-- Every instruction is exactly one ring operation. Register access is free. -/
def cost (P : Program n k) : ℕ := P.length

theorem eval_append (p : Fin k → R) (P Q : Program n k) (x : Fin n → R) :
    eval p (P ++ Q) x = eval p Q (eval p P x) := by
  induction P generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

@[simp] theorem transpose_cost (P : Program n k) : cost (transpose P) = cost P := by
  simp [cost, transpose]

@[simp] theorem transpose_transpose (P : Program n k) : transpose (transpose P) = P := by
  simp [transpose, List.map_reverse, List.map_map, Function.comp_def]

/-- Dot-product specification of the transposed computation, over arbitrary
commutative rings and with the fixed parameter values shared. -/
theorem adjoint (p : Fin k → R) (P : Program n k) (x y : Fin n → R) :
    eval p P x ⬝ᵥ y = x ⬝ᵥ eval p (transpose P) y := by
  induction P generalizing x y with
  | nil => rfl
  | cons g gs ih =>
    rw [eval, ih, Instruction.adjoint]
    simp [transpose, eval_append, eval]

end DivisionFree.LinearProgram
