import DivisionFree.LinearStraightLine.GateTranspose
import DivisionFree.LinearStraightLine.OutputTranspose

/-!
# Transposition of rectangular linear straight-line programs

The construction handles intermediate fanout and repeated outputs explicitly.
The reverse gate cost is at most twice the forward gate cost, and output accumulation
costs at most one addition per output. No parameter arithmetic is added.
-/

namespace DivisionFree.LinearStraightLine

open Matrix

variable {n m k : ℕ} {R : Type*} [CommRing R]

noncomputable def Program.transposeCircuit : {n m : ℕ} → Program k n m →
    Circuit (Fin k ⊕ Fin m) (Fin n)
  | _, _, .output w => outputTranspose w
  | _, _, .letGate g body =>
      .comp (.pair (.wire (fun c : Fin k => Sum.inl c)) body.transposeCircuit) g.pullbackCircuit

theorem Program.transposeCircuit_let_eval (g : Gate n k) (body : Program k (n + 1) m)
    (p : Fin k → R) (y : Fin m → R) :
    (Program.letGate g body).transposeCircuit.eval (Sum.elim p y) =
      g.pullback p (body.transposeCircuit.eval (Sum.elim p y)) := by
  funext i
  simp only [transposeCircuit, Circuit.eval_comp]
  change g.pullbackCircuit.eval
    (Sum.elim p (body.transposeCircuit.eval (Sum.elim p y))) i = _
  rw [Gate.pullbackCircuit_eval]

theorem Program.transposeCircuit_cost (P : Program k n m) :
    P.transposeCircuit.cost ≤ 2 * P.cost + m := by
  induction P with
  | output w => simpa [transposeCircuit, cost] using outputTranspose_cost (k := k) w
  | letGate g body ih =>
    simp only [transposeCircuit, Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost,
      Nat.zero_add, cost]
    have hg := g.pullbackCircuit_cost
    omega

/-- Universal correctness of the transposed circuit, including intermediate
reuse and repeated/zero rectangular outputs. -/
theorem Program.transposeCircuit_adjoint (P : Program k n m)
    (p : Fin k → R) (x : Fin n → R) (y : Fin m → R) :
    P.eval p x ⬝ᵥ y = x ⬝ᵥ P.transposeCircuit.eval (Sum.elim p y) := by
  induction P with
  | output w => exact outputTranspose_adjoint w p x y
  | letGate g body ih =>
    rw [transposeCircuit_let_eval]
    exact (ih (Fin.snoc x (g.eval p x)) y).trans
      (g.pullback_adjoint p x (body.transposeCircuit.eval (Sum.elim p y)))

/-- The arithmetic cost is stated in terms of the actual forward compiler,
whose cost equals the number of straight-line arithmetic instructions. -/
theorem Program.transposeCircuit_cost_le_compile (P : Program k n m) :
    P.transposeCircuit.cost ≤ 2 * P.compile.cost + m := by
  simpa using P.transposeCircuit_cost

/-- In the convention where subtraction costs one operation, the bound is
`3c + m`. The last adjoint register is discarded, so a subtraction's reverse
propagation needs only two additions and one negation. -/
theorem Program.transposeCircuit_cost_le_operations (P : Program k n m) :
    P.transposeCircuit.cost ≤ 3 * P.operations + m := by
  induction P with
  | output w => simpa [transposeCircuit, operations] using outputTranspose_cost (k := k) w
  | letGate g body ih =>
    simp only [transposeCircuit, Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost,
      Nat.zero_add, operations]
    have hg := g.pullbackCircuit_cost_le_operations
    omega

/-- If the forward program implements a matrix, the constructed reverse
circuit implements the usual rectangular matrix transpose. -/
theorem Program.transposeCircuit_eq_mulVec (P : Program k n m) (p : Fin k → R)
    (A : Matrix (Fin m) (Fin n) R)
    (hA : ∀ x, P.eval p x = A *ᵥ x) (y : Fin m → R) :
    P.transposeCircuit.eval (Sum.elim p y) = A.transpose *ᵥ y := by
  apply dotProduct_eq
  intro x
  calc
    P.transposeCircuit.eval (Sum.elim p y) ⬝ᵥ x =
        x ⬝ᵥ P.transposeCircuit.eval (Sum.elim p y) := dotProduct_comm _ _
    _ = P.eval p x ⬝ᵥ y := (P.transposeCircuit_adjoint p x y).symm
    _ = (A *ᵥ x) ⬝ᵥ y := by rw [hA]
    _ = y ⬝ᵥ (A *ᵥ x) := dotProduct_comm _ _
    _ = x ⬝ᵥ (A.transpose *ᵥ y) := (Matrix.dotProduct_transpose_mulVec A x y).symm
    _ = (A.transpose *ᵥ y) ⬝ᵥ x := dotProduct_comm _ _

end DivisionFree.LinearStraightLine
