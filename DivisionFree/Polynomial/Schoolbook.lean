import DivisionFree.Circuit
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# A concrete quadratic baseline for truncated multiplication

The circuit is independent of the coefficient ring. Every coefficient product
and addition is charged by the arithmetic syntax. This implementation inhabits
the multiplication interface; it is not an almost-linear multiplier.
-/

namespace DivisionFree

open scoped BigOperators

namespace Circuit

def sumList {I : Type} : List (Circuit I PUnit) → Circuit I PUnit
  | [] => .zero
  | p :: ps => sum p (sumList ps)

theorem sumList_eval {I : Type} {R : Type*} [Ring R]
    (ps : List (Circuit I PUnit)) (x : I → R) :
    (sumList ps).eval x PUnit.unit = (ps.map (fun p => p.eval x PUnit.unit)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumList, ih]

theorem sumList_cost {I : Type} (ps : List (Circuit I PUnit)) :
    (sumList ps).cost = (ps.map Circuit.cost).sum + ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumList, ih]; omega

end Circuit

namespace PolynomialArithmetic

universe u

noncomputable def vectorPolynomial {R : Type*} [Semiring R]
    (n : ℕ) (x : Fin n → R) : Polynomial R := by
  classical
  exact Polynomial.ofFn n x

def coefficientTerm (n : ℕ) (j : Fin n) (i : Fin (j.val + 1)) :
    Circuit (Bool × Fin n) PUnit :=
  .comp (.wire (fun b : Bool => if b then
      (true, ⟨j.val - i.val, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩)
    else (false, ⟨i.val, lt_of_lt_of_le i.isLt j.isLt⟩))) .mul

def coefficientCircuit (n : ℕ) (j : Fin n) : Circuit (Bool × Fin n) PUnit :=
  Circuit.sumList (List.ofFn (coefficientTerm n j))

def schoolbook (n : ℕ) : Circuit (Bool × Fin n) (Fin n) :=
  .comp (.bundle (coefficientCircuit n)) (.wire (fun j => (j, PUnit.unit)))

@[simp] theorem coefficientTerm_cost (n : ℕ) (j : Fin n) (i : Fin (j.val + 1)) :
    (coefficientTerm n j i).cost = 1 := by simp [coefficientTerm]

theorem coefficientCircuit_cost (n : ℕ) (j : Fin n) :
    (coefficientCircuit n j).cost = 2 * (j.val + 1) := by
  simp [coefficientCircuit, Circuit.sumList_cost, List.map_ofFn, List.sum_ofFn]
  omega

/-- The triangular set of coefficient products gives the exact cost. -/
theorem schoolbook_cost_exact (n : ℕ) : (schoolbook n).cost = n * (n + 1) := by
  simp only [schoolbook, Circuit.comp_cost, Circuit.bundle_cost, Circuit.wire_cost,
    Nat.add_zero, coefficientCircuit_cost]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

theorem schoolbook_cost_le (n : ℕ) : (schoolbook n).cost ≤ 2 * n ^ 2 := by
  simp only [schoolbook, Circuit.comp_cost, Circuit.bundle_cost, Circuit.wire_cost,
    Nat.add_zero, coefficientCircuit_cost]
  calc
    ∑ j : Fin n, 2 * (j.val + 1) ≤ ∑ _ : Fin n, 2 * n :=
      Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left 2 j.isLt)
    _ = 2 * n ^ 2 := by simp; ring

theorem schoolbook_correct {R : Type*} [CommRing R]
    (n : ℕ) (x : Bool × Fin n → R) (j : Fin n) :
    (schoolbook n).eval x j =
      (vectorPolynomial n (fun i => x (false, i)) *
       vectorPolynomial n (fun i => x (true, i))).coeff j.val := by
  classical
  unfold vectorPolynomial
  simp only [schoolbook, Circuit.eval_comp, Circuit.eval_wire, Circuit.eval_bundle,
    coefficientCircuit, Circuit.sumList_eval, List.map_ofFn, List.sum_ofFn]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [coefficientTerm,
    Polynomial.ofFn_coeff_eq_val_of_lt _ (lt_of_lt_of_le i.isLt j.isLt),
    Polynomial.ofFn_coeff_eq_val_of_lt _ (lt_of_le_of_lt (Nat.sub_le _ _) j.isLt)]

/-- An implementation includes a ring-independent circuit and its universal
correctness proof. Its cost is derived from that circuit, never supplied as
an unchecked annotation. -/
structure Multiplier (n : ℕ) where
  circuit : Circuit (Bool × Fin n) (Fin n)
  correct : ∀ (R : Type u) [CommRing R]
    (x : Bool × Fin n → R) (j : Fin n),
    circuit.eval x j =
      (vectorPolynomial n (fun i => x (false, i)) *
       vectorPolynomial n (fun i => x (true, i))).coeff j.val

def Multiplier.cost {n : ℕ} (A : Multiplier n) : ℕ := A.circuit.cost

def schoolbookMultiplier (n : ℕ) : Multiplier n where
  circuit := schoolbook n
  correct _ _ := schoolbook_correct n

theorem schoolbookMultiplier_cost_exact (n : ℕ) :
    (schoolbookMultiplier n).cost = n * (n + 1) :=
  schoolbook_cost_exact n

theorem schoolbookMultiplier_cost (n : ℕ) : (schoolbookMultiplier n).cost ≤ 2 * n ^ 2 :=
  schoolbook_cost_le n

end PolynomialArithmetic
end DivisionFree
