import DivisionFree.LinearCircuit.Compile
import DivisionFree.Constants

/-! Multiplication-gate resources for compilation and transposition. -/

namespace DivisionFree.LinearStraightLine

open LinearCircuit

variable {n m k : ℕ}

private def scaleCount {n k : ℕ} : LinearProgram.Program n k → ℕ
  | [] => 0
  | .scale _ _ :: gs => scaleCount gs + 1
  | _ :: gs => scaleCount gs

private theorem instruction_compile_multiplications {n k : ℕ}
    (g : LinearProgram.Instruction n k) :
    g.compile.multiplications = match g with
      | .scale _ _ => 1
      | _ => 0 := by
  cases g <;> simp [LinearProgram.Instruction.compile,
    LinearProgram.Instruction.operation, Circuit.multiplications]

private theorem linearProgram_compile_multiplications {n k : ℕ}
    (P : LinearProgram.Program n k) :
    (LinearProgram.compile P).multiplications = scaleCount P := by
  induction P with
  | nil => rfl
  | cons g gs ih =>
      cases g <;> simp [LinearProgram.compile, Circuit.comp_multiplications,
        instruction_compile_multiplications, scaleCount, ih]
      all_goals omega

private theorem scaleCount_append {n k : ℕ} (P Q : LinearProgram.Program n k) :
    scaleCount (P ++ Q) = scaleCount P + scaleCount Q := by
  induction P with
  | nil => simp [scaleCount]
  | cons g gs ih =>
      cases g <;> simp [scaleCount, ih]
      all_goals omega

private theorem scaleCount_mapTranspose {n k : ℕ} (P : LinearProgram.Program n k) :
    scaleCount (P.map LinearProgram.Instruction.transpose) = scaleCount P := by
  induction P with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [scaleCount, LinearProgram.Instruction.transpose, ih]

private theorem scaleCount_reverse {n k : ℕ} (P : LinearProgram.Program n k) :
    scaleCount P.reverse = scaleCount P := by
  induction P with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [scaleCount, scaleCount_append, ih]

private theorem scaleCount_transpose {n k : ℕ} (P : LinearProgram.Program n k) :
    scaleCount (LinearProgram.transpose P) = scaleCount P := by
  induction P with
  | nil => rfl
  | cons g gs ih =>
      rw [LinearProgram.transpose, scaleCount_mapTranspose, scaleCount_reverse]

private theorem gate_pullback_multiplications {n k : ℕ} (g : Gate n k) :
    g.pullbackCircuit.multiplications = g.circuit.multiplications := by
  simp only [Gate.pullbackCircuit, Circuit.comp_multiplications,
    Circuit.wire_multiplications, linearProgram_compile_multiplications]
  cases g <;> simp [Gate.reverseProgram, scaleCount_transpose,
    scaleCount, Gate.initialProgram, Gate.circuit,
    Circuit.multiplications]

private theorem sumList_wire_multiplications {J I : Type} (js : List J)
    (select : J → I) :
    (Circuit.sumList (js.map fun j => Circuit.wire (fun _ : PUnit => select j))).multiplications = 0 := by
  induction js with
  | nil => simp [Circuit.sumList]
  | cons j js ih => simp [Circuit.sumList, ih]

private theorem fiberCircuit_multiplications {n m k : ℕ}
    (w : Fin m → Option (Fin n)) (i : Fin n) :
    (fiberCircuit (k := k) w i).multiplications = 0 := by
  classical
  simpa [fiberCircuit] using
    (sumList_wire_multiplications
      ((Finset.univ.filter (fun j => w j = some i)).toList)
      (fun j => (Sum.inr j : Fin k ⊕ Fin m)))

private theorem sumList_wire_constantBits {J I : Type} (js : List J)
    (select : J → I) :
    (Circuit.sumList (js.map fun j => Circuit.wire (fun _ : PUnit => select j))).constantBits = 0 := by
  induction js with
  | nil => simp [Circuit.sumList, Circuit.constantBits]
  | cons j js ih =>
      simp [Circuit.sumList, Circuit.sum, Circuit.constantBits, ih]

private theorem fiberCircuit_constantBits {n m k : ℕ}
    (w : Fin m → Option (Fin n)) (i : Fin n) :
    (fiberCircuit (k := k) w i).constantBits = 0 := by
  classical
  simpa [fiberCircuit] using
    (sumList_wire_constantBits
      ((Finset.univ.filter (fun j => w j = some i)).toList)
      (fun j => (Sum.inr j : Fin k ⊕ Fin m)))

private theorem instruction_compile_constantBits {n k : ℕ}
    (g : LinearProgram.Instruction n k) : g.compile.constantBits = 0 := by
  cases g <;> simp [LinearProgram.Instruction.compile,
    LinearProgram.Instruction.operation, Circuit.constantBits]

private theorem linearProgram_compile_constantBits {n k : ℕ}
    (P : LinearProgram.Program n k) : (LinearProgram.compile P).constantBits = 0 := by
  induction P with
  | nil => simp [LinearProgram.compile, Circuit.constantBits]
  | cons g gs ih =>
      simp [LinearProgram.compile, Circuit.comp_constantBits,
        instruction_compile_constantBits, ih]

private theorem gate_pullback_constantBits {n k : ℕ} (g : Gate n k) :
    g.pullbackCircuit.constantBits = 0 := by
  simp [Gate.pullbackCircuit, linearProgram_compile_constantBits, Circuit.constantBits]

@[simp] theorem outputTranspose_multiplications {n m k : ℕ}
    (w : Fin m → Option (Fin n)) :
    (outputTranspose (k := k) w).multiplications = 0 := by
  classical
  simp [outputTranspose, fiberCircuit_multiplications, Circuit.multiplications]

theorem Program.transposeCircuit_multiplications (P : Program k n m) :
    P.transposeCircuit.multiplications = P.compile.multiplications := by
  induction P with
  | output w =>
      simp [Program.transposeCircuit, Program.compile, outputTranspose_multiplications,
        outputCircuit, Circuit.multiplications]
  | letGate g body ih =>
      cases g <;> simp [Program.transposeCircuit, Program.compile,
        Circuit.comp_multiplications, Gate.extend,
        Gate.circuit, gate_pullback_multiplications, ih, Circuit.multiplications]
      all_goals omega

theorem Program.compile_constantBits (P : Program k n m) :
    P.compile.constantBits = 0 := by
  induction P with
  | output w => simp [Program.compile, outputCircuit, Circuit.constantBits]
  | letGate g body ih =>
      cases g <;> simp [Program.compile, Gate.extend, Gate.circuit, Circuit.constantBits,
        Circuit.sum, Circuit.negative, ih]

theorem Program.transposeCircuit_constantBits (P : Program k n m) :
    P.transposeCircuit.constantBits = 0 := by
  induction P with
  | output w =>
      simp [Program.transposeCircuit, outputTranspose, fiberCircuit_constantBits,
        Circuit.constantBits]
  | letGate g body ih =>
      cases g <;> simp [Program.transposeCircuit, gate_pullback_constantBits,
        Circuit.comp_constantBits, Circuit.constantBits, ih]

end DivisionFree.LinearStraightLine
