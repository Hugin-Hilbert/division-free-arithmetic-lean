import DivisionFree.LinearCompile

/-!
# Linear straight-line programs with fresh registers

Each arithmetic instruction appends its result to the available registers.
Operands may reuse any earlier register. Outputs may repeat registers or be
zero. Fixed scalar parameters are explicit inputs, independent of the vector
to which the linear map is applied.
-/

namespace DivisionFree.LinearStraightLine

inductive Gate (n k : ℕ) where
  | zero
  | add (a b : Fin n)
  | sub (a b : Fin n)
  | neg (a : Fin n)
  | scale (c : Fin k) (a : Fin n)

variable {n m k : ℕ} {R : Type*} [CommRing R]

def Gate.eval (p : Fin k → R) (x : Fin n → R) : Gate n k → R
  | .zero => 0
  | .add a b => x a + x b
  | .sub a b => x a - x b
  | .neg a => -x a
  | .scale c a => p c * x a

def Gate.circuit : Gate n k → Circuit (Fin k ⊕ Fin n) PUnit
  | .zero => .zero
  | .add a b => .comp (.wire (fun j : Bool => .inr (if j then b else a))) .add
  | .sub a b => Circuit.sum (.wire (fun _ => .inr a))
      (Circuit.negative (.wire (fun _ => .inr b)))
  | .neg a => .comp (.wire (fun _ => .inr a)) .neg
  | .scale c a => .comp (.wire (fun j : Bool => if j then .inr a else .inl c)) .mul

/-- Subtraction is charged as one addition and one negation in `Circuit`. -/
def Gate.cost : Gate n k → ℕ
  | .zero => 0
  | .sub _ _ => 2
  | _ => 1

/-- The usual arithmetic model charges subtraction as one operation. -/
def Gate.operations : Gate n k → ℕ
  | .zero => 0
  | _ => 1

theorem Gate.cost_le_two_operations (g : Gate n k) : g.cost ≤ 2 * g.operations := by
  cases g <;> simp [cost, operations]

@[simp] theorem Gate.circuit_cost (g : Gate n k) : g.circuit.cost = g.cost := by
  cases g <;> simp [circuit, cost]

@[simp] theorem Gate.circuit_eval (g : Gate n k) (p : Fin k → R) (x : Fin n → R) :
    g.circuit.eval (Sum.elim p x) PUnit.unit = g.eval p x := by
  cases g <;> simp [circuit, eval, sub_eq_add_neg]

/-- Retain the parameters and the old registers, appending the result. -/
def Gate.extend (g : Gate n k) : Circuit (Fin k ⊕ Fin n) (Fin k ⊕ Fin (n + 1)) :=
  .comp (.pair (.wire id) g.circuit) (.wire (fun s => match s with
    | .inl c => .inl (.inl c)
    | .inr i => Fin.lastCases (.inr PUnit.unit) (fun j => .inl (.inr j)) i))

@[simp] theorem Gate.extend_cost (g : Gate n k) : g.extend.cost = g.cost := by
  simp [extend]

theorem Gate.extend_eval (g : Gate n k) (p : Fin k → R) (x : Fin n → R) :
    g.extend.eval (Sum.elim p x) = Sum.elim p (Fin.snoc x (g.eval p x)) := by
  funext s
  cases s with
  | inl c => simp [extend]
  | inr i =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [extend]
    · simp [extend]

/-- `none` denotes a zero output; repetition models output fanout. -/
def outputValue (w : Fin m → Option (Fin n)) (x : Fin n → R) (j : Fin m) : R :=
  (w j).elim 0 x

def outputCircuit (w : Fin m → Option (Fin n)) : Circuit (Fin k ⊕ Fin n) (Fin m) :=
  .comp (.pair (.wire (fun i : Fin n => Sum.inr i)) (.zero : Circuit _ PUnit))
    (.wire (fun j => (w j).elim (.inr PUnit.unit) Sum.inl))

@[simp] theorem outputCircuit_cost (w : Fin m → Option (Fin n)) :
    (outputCircuit (k := k) w).cost = 0 := by simp [outputCircuit]

@[simp] theorem outputCircuit_eval (w : Fin m → Option (Fin n))
    (p : Fin k → R) (x : Fin n → R) (j : Fin m) :
    (outputCircuit w).eval (Sum.elim p x) j = outputValue w x j := by
  cases h : w j <;> simp [outputCircuit, outputValue, h]

inductive Program (k : ℕ) : ℕ → ℕ → Type where
  | output {n m : ℕ} (select : Fin m → Option (Fin n)) : Program k n m
  | letGate {n m : ℕ} (gate : Gate n k) (body : Program k (n + 1) m) : Program k n m

def Program.eval (p : Fin k → R) : {n m : ℕ} → Program k n m → (Fin n → R) → Fin m → R
  | _, _, .output w, x => outputValue w x
  | _, _, .letGate g body, x => body.eval p (Fin.snoc x (g.eval p x))

/-- Arithmetic cost, with subtraction expanded into addition and negation. -/
def Program.cost : {n m : ℕ} → Program k n m → ℕ
  | _, _, .output _ => 0
  | _, _, .letGate g body => g.cost + body.cost

def Program.operations : {n m : ℕ} → Program k n m → ℕ
  | _, _, .output _ => 0
  | _, _, .letGate g body => g.operations + body.operations

theorem Program.cost_le_two_operations (P : Program k n m) : P.cost ≤ 2 * P.operations := by
  induction P with
  | output w => rfl
  | letGate g body ih =>
    have hg := g.cost_le_two_operations
    simp only [cost, operations]
    omega

def Program.compile : {n m : ℕ} → Program k n m → Circuit (Fin k ⊕ Fin n) (Fin m)
  | _, _, .output w => outputCircuit w
  | _, _, .letGate g body => .comp g.extend body.compile

@[simp] theorem Program.compile_cost (P : Program k n m) : P.compile.cost = P.cost := by
  induction P with
  | output w => simp [compile, cost]
  | letGate g body ih => simp [compile, cost, ih]

theorem Program.compile_eval (P : Program k n m) (p : Fin k → R) (x : Fin n → R) :
    P.compile.eval (Sum.elim p x) = P.eval p x := by
  induction P with
  | output w => funext j; simp [compile, eval]
  | letGate g body ih =>
    funext j
    simp only [compile, Circuit.eval_comp]
    rw [Gate.extend_eval, ih]
    rfl

end DivisionFree.LinearStraightLine
