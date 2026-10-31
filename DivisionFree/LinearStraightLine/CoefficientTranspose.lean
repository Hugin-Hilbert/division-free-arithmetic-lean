import DivisionFree.LinearStraightLine.Transpose
import DivisionFree.Polynomial.CoefficientMatrix

/-! Transposition of truncated-polynomial matrices using only a program
for the base-ring coefficient map. Block reversal is implemented by wires. -/

namespace DivisionFree.LinearStraightLine

open PolynomialArithmetic

variable {r s q k : ℕ} {R : Type*} [CommRing R]

def reverseInputs (k r q : ℕ) : Circuit (Fin k ⊕ Fin (r * q)) (Fin k ⊕ Fin (r * q)) :=
  .wire (fun a => match a with
    | .inl c => .inl c
    | .inr t => .inr (reverseIndex r q t))

theorem reverseInputs_eval (p : Fin k → R) (y : Fin (r * q) → R) :
    (reverseInputs k r q).eval (Sum.elim p y) = Sum.elim p (reverseFlat y) := by
  funext a
  cases a <;> rfl

noncomputable def Program.transposeCoefficients (P : Program k (s * q) (r * q)) :
    Circuit (Fin k ⊕ Fin (r * q)) (Fin (s * q)) :=
  .comp (reverseInputs k r q) (.comp P.transposeCircuit (.wire (reverseIndex s q)))

theorem Program.transposeCoefficients_eval (P : Program k (s * q) (r * q))
    (p : Fin k → R) (y : Fin (r * q) → R) :
    P.transposeCoefficients.eval (Sum.elim p y) =
      reverseFlat (P.transposeCircuit.eval (Sum.elim p (reverseFlat y))) := by
  funext i
  simp only [transposeCoefficients, Circuit.eval_comp, Circuit.eval_wire]
  rw [reverseInputs_eval]
  rfl

/-- Both reversals are free wiring, so the base-ring bound is unchanged. -/
theorem Program.transposeCoefficients_cost (P : Program k (s * q) (r * q)) :
    P.transposeCoefficients.cost ≤ 3 * P.operations + r * q := by
  simpa [transposeCoefficients, reverseInputs] using P.transposeCircuit_cost_le_operations

/-- Correctness of the reverse/transpose/reverse construction for the actual
truncated coefficient map, without storing its expanded dense matrix. -/
theorem Program.transposeCoefficients_correct (hq : 0 < q)
    (P : Program k (s * q) (r * q)) (p : Fin k → R)
    (A : Fin r → Fin s → Fin q → R)
    (hP : ∀ x, P.eval p x = coefficientMap A x) (y : Fin (r * q) → R) :
    P.transposeCoefficients.eval (Sum.elim p y) = coefficientMap (blockTranspose A) y := by
  have hd : P.transposeCircuit.eval (Sum.elim p (reverseFlat y)) =
      reverseFlat (coefficientMap (blockTranspose A) y) := by
    apply dotProduct_eq
    intro x
    calc
      P.transposeCircuit.eval (Sum.elim p (reverseFlat y)) ⬝ᵥ x =
          x ⬝ᵥ P.transposeCircuit.eval (Sum.elim p (reverseFlat y)) := dotProduct_comm _ _
      _ = P.eval p x ⬝ᵥ reverseFlat y :=
        (P.transposeCircuit_adjoint p x (reverseFlat y)).symm
      _ = coefficientMap A x ⬝ᵥ reverseFlat y := by rw [hP]
      _ = x ⬝ᵥ reverseFlat (coefficientMap (blockTranspose A) y) :=
        coefficientMap_pairing hq A x y
      _ = reverseFlat (coefficientMap (blockTranspose A) y) ⬝ᵥ x := dotProduct_comm _ _
  rw [transposeCoefficients_eval, hd, reverseFlat_involutive]

end DivisionFree.LinearStraightLine
