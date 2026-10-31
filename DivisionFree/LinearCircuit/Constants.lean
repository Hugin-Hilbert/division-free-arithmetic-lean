import DivisionFree.LinearCircuit.Basic
import DivisionFree.Constants

/-! Linear circuits have no hidden integer constant leaves. -/

namespace DivisionFree.LinearCircuit

theorem compile_constantBits {K I O : Type} [Fintype K] (C : LinearCircuit K I O) :
    C.compile.constantBits = 0 := by
  induction C with
  | wire _ => rfl
  | zero => rfl
  | add => rfl
  | neg => rfl
  | scale _ => rfl
  | comp first second ihFirst ihSecond =>
      simp [compile, Circuit.constantBits, ihFirst, ihSecond]
  | pair left right ihLeft ihRight =>
      simp [compile, Circuit.constantBits, ihLeft, ihRight]
  | bundle branches ih => simp [compile, Circuit.constantBits, ih]

end DivisionFree.LinearCircuit
