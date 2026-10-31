import DivisionFree.LinearStraightLine.Basic

/-! Code prefixes append fresh registers and retain all old registers.
This permits circuit compilation without charging, or evaluating, wires twice. -/

namespace DivisionFree.LinearStraightLine

inductive Prefix (k : ℕ) : ℕ → ℕ → Type where
  | nil {n : ℕ} : Prefix k n n
  | step {n m : ℕ} (gate : Gate n k) (body : Prefix k (n + 1) m) : Prefix k n m

namespace Prefix

variable {k n m l r : ℕ}

theorem le : {n m : ℕ} → Prefix k n m → n ≤ m
  | _, _, .nil => le_rfl
  | _, _, .step _ body => Nat.le_trans (Nat.le_succ _) body.le

def eval {R : Type*} [CommRing R] (p : Fin k → R) :
    {n m : ℕ} → Prefix k n m → (Fin n → R) → Fin m → R
  | _, _, .nil, x => x
  | _, _, .step g body, x => body.eval p (Fin.snoc x (g.eval p x))

def cost : {n m : ℕ} → Prefix k n m → ℕ
  | _, _, .nil => 0
  | _, _, .step g body => g.cost + body.cost

/-- Multiplication gates in the appended straight-line prefix. -/
def multiplications : {n m : ℕ} → Prefix k n m → ℕ
  | _, _, .nil => 0
  | _, _, .step g body => g.circuit.multiplications + body.multiplications

def length : {n m : ℕ} → Prefix k n m → ℕ
  | _, _, .nil => 0
  | _, _, .step _ body => body.length + 1

def append : {n m : ℕ} → Prefix k n m → Prefix k m l → Prefix k n l
  | _, _, .nil, Q => Q
  | _, _, .step g body, Q => .step g (body.append Q)

def finish : {n m : ℕ} → Prefix k n m →
    (Fin r → Option (Fin m)) → Program k n r
  | _, _, .nil, w => .output w
  | _, _, .step g body, w => .letGate g (body.finish w)

@[simp] theorem append_cost (P : Prefix k n m) (Q : Prefix k m l) :
    (P.append Q).cost = P.cost + Q.cost := by
  induction P with
  | nil => simp [append, cost]
  | step g body ih => simp [append, cost, ih, Nat.add_assoc]

@[simp] theorem append_multiplications (P : Prefix k n m) (Q : Prefix k m l) :
    (P.append Q).multiplications = P.multiplications + Q.multiplications := by
  induction P with
  | nil => simp [append, multiplications]
  | step g body ih => simp [append, multiplications, ih, Nat.add_assoc]

@[simp] theorem append_length (P : Prefix k n m) (Q : Prefix k m l) :
    (P.append Q).length = P.length + Q.length := by
  induction P with
  | nil => simp [append, length]
  | step g body ih => simp only [append, length, ih]; omega

theorem dimension (P : Prefix k n m) : m = n + P.length := by
  induction P with
  | nil => simp [length]
  | step g body ih => simp only [length]; omega

@[simp] theorem finish_cost (P : Prefix k n m) (w : Fin r → Option (Fin m)) :
    (P.finish w).cost = P.cost := by
  induction P with
  | nil => rfl
  | step g body ih => simp [finish, Program.cost, cost, ih]

@[simp] theorem finish_multiplications (P : Prefix k n m)
    (w : Fin r → Option (Fin m)) :
    (P.finish w).compile.multiplications = P.multiplications := by
  induction P with
  | nil => simp [finish, Program.compile, outputCircuit, multiplications]
  | step g body ih =>
      simp [finish, Program.compile, Gate.extend, Circuit.multiplications,
        multiplications, ih]

theorem append_eval {R : Type*} [CommRing R]
    (P : Prefix k n m) (Q : Prefix k m l) (p : Fin k → R) (x : Fin n → R) :
    (P.append Q).eval p x = Q.eval p (P.eval p x) := by
  induction P with
  | nil => rfl
  | step g body ih => exact ih Q _

theorem finish_eval {R : Type*} [CommRing R]
    (P : Prefix k n m) (w : Fin r → Option (Fin m))
    (p : Fin k → R) (x : Fin n → R) :
    (P.finish w).eval p x = outputValue w (P.eval p x) := by
  induction P with
  | nil => rfl
  | step g body ih => exact ih w _

/-- Every old register survives the prefix unchanged. -/
theorem eval_old {R : Type*} [CommRing R] (P : Prefix k n m)
    (p : Fin k → R) (x : Fin n → R) (i : Fin n) :
    P.eval p x (Fin.castLE P.le i) = x i := by
  induction P with
  | nil => rfl
  | @step n m g body ih =>
    change body.eval p (Fin.snoc x (g.eval p x))
      (Fin.castLE body.le i.castSucc) = x i
    rw [ih]
    simp

end Prefix
end DivisionFree.LinearStraightLine
