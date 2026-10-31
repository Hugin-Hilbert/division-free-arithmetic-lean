import DivisionFree.LinearStraightLine.Basic

/-! Reverse propagation through one appended arithmetic instruction. The
auxiliary register program is used to prove the adjoint. The implementation
omits restoration of the discarded last register after a subtraction. -/

namespace DivisionFree.LinearStraightLine

variable {n k : ℕ} {R : Type*} [CommRing R]

def Gate.initialProgram : Gate n k → LinearProgram.Program (n + 1) k
  | .zero => []
  | .add a b => [.add (Fin.last n) a.castSucc, .add (Fin.last n) b.castSucc]
  | .sub a b => [.add (Fin.last n) a.castSucc, .neg (Fin.last n),
      .add (Fin.last n) b.castSucc, .neg (Fin.last n)]
  | .neg a => [.add (Fin.last n) a.castSucc, .neg (Fin.last n)]
  | .scale c a => [.add (Fin.last n) a.castSucc, .scale (Fin.last n) c]

theorem Gate.initialProgram_eval (g : Gate n k) (p : Fin k → R) (x : Fin n → R) :
    LinearProgram.eval p g.initialProgram (Fin.snoc x 0) = Fin.snoc x (g.eval p x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · cases g <;> simp [initialProgram, LinearProgram.eval, LinearProgram.Instruction.eval,
      eval, sub_eq_add_neg, add_comm]
  · cases g <;> simp [initialProgram, LinearProgram.eval, LinearProgram.Instruction.eval]

def Gate.pullback (g : Gate n k) (p : Fin k → R) (y : Fin (n + 1) → R) : Fin n → R :=
  fun i => LinearProgram.eval p (LinearProgram.transpose g.initialProgram) y i.castSucc

theorem Gate.pullback_adjoint (g : Gate n k) (p : Fin k → R)
    (x : Fin n → R) (y : Fin (n + 1) → R) :
    Fin.snoc x (g.eval p x) ⬝ᵥ y = x ⬝ᵥ g.pullback p y := by
  have h := LinearProgram.adjoint p g.initialProgram (Fin.snoc x 0) y
  rw [g.initialProgram_eval] at h
  rw [h]
  simp [dotProduct, Fin.sum_univ_castSucc, pullback]

def Gate.reverseProgram : Gate n k → LinearProgram.Program (n + 1) k
  | .sub a b => [.add a.castSucc (Fin.last n), .neg (Fin.last n),
      .add b.castSucc (Fin.last n)]
  | g => LinearProgram.transpose g.initialProgram

def Gate.pullbackCircuit (g : Gate n k) : Circuit (Fin k ⊕ Fin (n + 1)) (Fin n) :=
  .comp (LinearProgram.compile g.reverseProgram)
    (.wire (fun i => Sum.inr i.castSucc))

theorem Gate.pullbackCircuit_cost (g : Gate n k) :
    g.pullbackCircuit.cost ≤ 2 * g.cost := by
  cases g <;> simp [pullbackCircuit, reverseProgram, initialProgram, cost,
    LinearProgram.cost, LinearProgram.transpose]

theorem Gate.pullbackCircuit_cost_le_operations (g : Gate n k) :
    g.pullbackCircuit.cost ≤ 3 * g.operations := by
  cases g <;> simp [pullbackCircuit, reverseProgram, initialProgram, operations,
    LinearProgram.cost, LinearProgram.transpose]

theorem Gate.pullbackCircuit_eval (g : Gate n k) (p : Fin k → R) (y : Fin (n + 1) → R) :
    g.pullbackCircuit.eval (Sum.elim p y) = g.pullback p y := by
  funext i
  cases g with
  | sub a b =>
    simp only [pullbackCircuit, Circuit.eval_comp, Circuit.eval_wire,
      LinearProgram.compile_eval, Sum.elim_inr, pullback,
      reverseProgram, initialProgram, LinearProgram.transpose, List.reverse_cons,
      List.reverse_nil, List.nil_append]
    simp only [List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, LinearProgram.Instruction.transpose, LinearProgram.eval,
      LinearProgram.Instruction.eval]
    have ha : Fin.last n ≠ a.castSucc := Ne.symm (Fin.castSucc_ne_last a)
    have hb : Fin.last n ≠ b.castSucc := Ne.symm (Fin.castSucc_ne_last b)
    by_cases hab : a = b
    · subst b
      by_cases hia : i = a <;>
        simp [Fin.castSucc_inj, hia, ha]
    · by_cases hia : i = a <;> by_cases hib : i = b <;>
        simp [Fin.castSucc_inj, hia, hib, hab, Ne.symm hab, ha, hb]
  | zero => simp [pullbackCircuit, reverseProgram, LinearProgram.compile_eval, pullback]
  | add a b => simp [pullbackCircuit, reverseProgram, LinearProgram.compile_eval, pullback]
  | neg a => simp [pullbackCircuit, reverseProgram, LinearProgram.compile_eval, pullback]
  | scale c a => simp [pullbackCircuit, reverseProgram, LinearProgram.compile_eval, pullback]

end DivisionFree.LinearStraightLine
