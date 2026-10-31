import DivisionFree.LinearCircuit.Basic
import DivisionFree.LinearStraightLine.Prefix
import DivisionFree.LinearStraightLine.Transpose

/-! Flatten linear circuits into fresh-register programs. Every intermediate
is computed once; wiring and repeated outputs only select existing registers. -/

namespace DivisionFree.LinearCircuit

open LinearStraightLine
open Matrix
open scoped BigOperators

universe u

variable {k : ℕ} {I O J : Type}

/-- A compiled prefix with an output register for every requested output.
The distinguished zero register lets zero outputs remain free. -/
structure Lowered (C : LinearCircuit (Fin k) I O)
    (n : ℕ) (zero : Fin n) (inputs : I → Fin n) where
  registers : ℕ
  code : Prefix k n registers
  outputs : O → Fin registers
  cost_eq : code.cost = C.cost
  multiplications_eq : code.multiplications = C.multiplications
  correct : ∀ (R : Type u) [CommRing R] (p : Fin k → R) (x : Fin n → R),
    x zero = 0 → ∀ o,
      code.eval p x (outputs o) = C.eval p (fun i => x (inputs i)) o

private structure BundleLowered (C : J → LinearCircuit (Fin k) I O)
    (js : List J) (n : ℕ) (zero : Fin n) (inputs : I → Fin n) where
  registers : ℕ
  code : Prefix k n registers
  outputs : J × O → Fin registers
  cost_eq : code.cost = (js.map fun j => (C j).cost).sum
  multiplications_eq : code.multiplications =
    (js.map fun j => (C j).multiplications).sum
  correct : ∀ (R : Type u) [CommRing R] (p : Fin k → R) (x : Fin n → R),
    x zero = 0 → ∀ j o, j ∈ js →
      code.eval p x (outputs (j, o)) = (C j).eval p (fun i => x (inputs i)) o

private noncomputable def lowerBundle [DecidableEq J]
    (C : J → LinearCircuit (Fin k) I O)
    (lower : ∀ j n zero inputs, Lowered.{u} (C j) n zero inputs) :
    ∀ (js : List J) (n : ℕ) (zero : Fin n) (inputs : I → Fin n),
      BundleLowered.{u} C js n zero inputs
  | [], n, zreg, _ =>
      { registers := n
        code := .nil
        outputs := fun _ => zreg
        cost_eq := rfl
        multiplications_eq := rfl
        correct := by simp }
  | j :: js, n, zreg, inputs => by
      let A := lower j n zreg inputs
      let B := lowerBundle C lower js A.registers (Fin.castLE A.code.le zreg)
        (fun i => Fin.castLE A.code.le (inputs i))
      refine
        { registers := B.registers
          code := A.code.append B.code
          outputs := fun jo => if jo.1 = j then Fin.castLE B.code.le (A.outputs jo.2)
            else B.outputs jo
          cost_eq := ?_
          multiplications_eq := ?_
          correct := ?_ }
      · rw [Prefix.append_cost, A.cost_eq, B.cost_eq]
        rfl
      · rw [Prefix.append_multiplications, A.multiplications_eq, B.multiplications_eq]
        rfl
      · intro R _ p x hx l o hl
        rw [Prefix.append_eval]
        by_cases hlj : l = j
        · subst l
          simp only [↓reduceIte]
          rw [Prefix.eval_old]
          exact A.correct R p x hx o
        · simp only [hlj, ↓reduceIte]
          have hx' : A.code.eval p x (Fin.castLE A.code.le zreg) = 0 := by
            rw [Prefix.eval_old, hx]
          have h := B.correct R p (A.code.eval p x) hx' l o (by simpa [hlj] using hl)
          have hinput : (fun i => A.code.eval p x (Fin.castLE A.code.le (inputs i))) =
              (fun i => x (inputs i)) := funext fun i => Prefix.eval_old A.code p x (inputs i)
          simpa only [hinput] using h

/-- Compile using existing input registers; recursion preserves intermediate
sharing even when a later wire repeats an earlier output. -/
noncomputable def lower (C : LinearCircuit (Fin k) I O) :
    ∀ (n : ℕ) (zero : Fin n) (inputs : I → Fin n), Lowered.{u} C n zero inputs := by
  classical
  induction C with
  | wire select =>
      intro n zero inputs
      exact ⟨n, .nil, fun o => inputs (select o), rfl, rfl, by intros; rfl⟩
  | zero =>
      intro n zero inputs
      exact ⟨n, .nil, fun _ => zero, rfl, rfl, by intro R _ p x hx o; exact hx⟩
  | add =>
      intro n zero inputs
      refine ⟨n + 1, .step (.add (inputs false) (inputs true)) .nil,
        fun _ => Fin.last n, rfl, ?_, ?_⟩
      · simp [Prefix.multiplications, Gate.circuit, Circuit.multiplications,
          LinearCircuit.multiplications]
      ·
        intro R _ p x hx o
        simp [Prefix.eval, Gate.eval, eval]
  | neg =>
      intro n zero inputs
      refine ⟨n + 1, .step (.neg (inputs PUnit.unit)) .nil,
        fun _ => Fin.last n, rfl, ?_, ?_⟩
      · simp [Prefix.multiplications, Gate.circuit, Circuit.multiplications,
          LinearCircuit.multiplications]
      · intro R _ p x hx o
        simp [Prefix.eval, Gate.eval, eval]
  | scale c =>
      intro n zero inputs
      refine ⟨n + 1, .step (.scale c (inputs PUnit.unit)) .nil,
        fun _ => Fin.last n, rfl, ?_, ?_⟩
      · simp [Prefix.multiplications, Gate.circuit, Circuit.multiplications,
          LinearCircuit.multiplications]
      · intro R _ p x hx o
        simp [Prefix.eval, Gate.eval, eval]
  | comp first second ihFirst ihSecond =>
      intro n zero inputs
      let A := ihFirst n zero inputs
      let B := ihSecond A.registers (Fin.castLE A.code.le zero) A.outputs
      refine ⟨B.registers, A.code.append B.code, B.outputs, ?_, ?_, ?_⟩
      · simp only [Prefix.append_cost, A.cost_eq, B.cost_eq, cost]
      · simp only [Prefix.append_multiplications, A.multiplications_eq,
          B.multiplications_eq, multiplications]
      · intro R _ p x hx o
        rw [Prefix.append_eval]
        have hx' : A.code.eval p x (Fin.castLE A.code.le zero) = 0 := by
          rw [Prefix.eval_old, hx]
        have h := B.correct R p (A.code.eval p x) hx' o
        have hinput := funext (A.correct R p x hx)
        simpa only [hinput, eval_comp] using h
  | pair left right ihLeft ihRight =>
      intro n zero inputs
      let A := ihLeft n zero inputs
      let B := ihRight A.registers (Fin.castLE A.code.le zero)
        (fun i => Fin.castLE A.code.le (inputs i))
      refine ⟨B.registers, A.code.append B.code,
        Sum.elim (fun o => Fin.castLE B.code.le (A.outputs o)) B.outputs, ?_, ?_, ?_⟩
      · simp only [Prefix.append_cost, A.cost_eq, B.cost_eq, cost]
      · simp only [Prefix.append_multiplications, A.multiplications_eq,
          B.multiplications_eq, multiplications]
      · intro R _ p x hx o
        rw [Prefix.append_eval]
        cases o with
        | inl o =>
            simp only [Sum.elim_inl, Prefix.eval_old, eval_pair_inl]
            exact A.correct R p x hx o
        | inr o =>
            simp only [Sum.elim_inr, eval_pair_inr]
            have hx' : A.code.eval p x (Fin.castLE A.code.le zero) = 0 := by
              rw [Prefix.eval_old, hx]
            have h := B.correct R p (A.code.eval p x) hx' o
            have hinput : (fun i => A.code.eval p x (Fin.castLE A.code.le (inputs i))) =
                (fun i => x (inputs i)) := funext fun i => Prefix.eval_old A.code p x (inputs i)
            simpa only [hinput] using h
  | bundle branches ih =>
      intro n zero inputs
      let B := lowerBundle branches ih Finset.univ.toList n zero inputs
      refine ⟨B.registers, B.code, B.outputs, ?_, ?_, ?_⟩
      · rw [B.cost_eq]
        simp [cost]
      · rw [B.multiplications_eq]
        simp [multiplications]
      · intro R _ p x hx jo
        exact B.correct R p x hx jo.1 jo.2 (by simp)

/-- Start with one free zero register, then return the selected outputs. -/
noncomputable def toProgram {n m : ℕ} (C : LinearCircuit (Fin k) (Fin n) (Fin m)) :
    Program k n m :=
  let P := lower.{u} C (n + 1) (Fin.last n) Fin.castSucc
  .letGate .zero (P.code.finish fun j => some (P.outputs j))

theorem toProgram_cost {n m : ℕ} (C : LinearCircuit (Fin k) (Fin n) (Fin m)) :
    (toProgram.{u} C).cost = C.cost := by
  simp only [toProgram, Program.cost, Gate.cost, Prefix.finish_cost, Nat.zero_add]
  exact (lower C (n + 1) (Fin.last n) Fin.castSucc).cost_eq

theorem toProgram_compile_multiplications {n m : ℕ}
    (C : LinearCircuit (Fin k) (Fin n) (Fin m)) :
    (toProgram.{u} C).compile.multiplications = C.multiplications := by
  simp only [toProgram, Program.compile, Circuit.comp_multiplications,
    Gate.extend, Gate.circuit, Circuit.pair_multiplications,
    Circuit.wire_multiplications, Circuit.zero_multiplications,
    Nat.zero_add, Prefix.finish_multiplications]
  exact (lower.{u} C (n + 1) (Fin.last n) Fin.castSucc).multiplications_eq

theorem toProgram_eval {n m : ℕ} (C : LinearCircuit (Fin k) (Fin n) (Fin m))
    {R : Type u} [CommRing R] (p : Fin k → R) (x : Fin n → R) :
    (toProgram.{u} C).eval p x = C.eval p x := by
  let P := lower.{u} C (n + 1) (Fin.last n) Fin.castSucc
  have hx : (Fin.snoc x 0 : Fin (n + 1) → R) (Fin.last n) = 0 := by simp
  have h := P.correct R p (Fin.snoc x 0) hx
  funext j
  change (P.code.finish (fun o => some (P.outputs o))).eval p (Fin.snoc x 0) j = _
  rw [Prefix.finish_eval]
  simpa only [outputValue, Option.elim_some, Fin.snoc_castSucc] using h j

/-- The existing reverse program now applies to every linear circuit without
inflation from wire fanout or shared intermediate values. -/
theorem transpose_cost {n m : ℕ} (C : LinearCircuit (Fin k) (Fin n) (Fin m)) :
    (toProgram.{u} C).transposeCircuit.cost ≤ 2 * C.cost + m := by
  simpa only [toProgram_cost] using (toProgram.{u} C).transposeCircuit_cost

theorem transpose_adjoint {n m : ℕ} (C : LinearCircuit (Fin k) (Fin n) (Fin m))
    {R : Type u} [CommRing R] (p : Fin k → R) (x : Fin n → R) (y : Fin m → R) :
    (C.eval p x) ⬝ᵥ y =
      x ⬝ᵥ ((toProgram.{u} C).transposeCircuit.eval (Sum.elim p y)) := by
  rw [← toProgram_eval C p x]
  exact (toProgram.{u} C).transposeCircuit_adjoint p x y

end DivisionFree.LinearCircuit
