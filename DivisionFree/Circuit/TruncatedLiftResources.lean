import DivisionFree.Circuit.TruncatedLift

/-! Exact base-ring resource accounting for coefficientwise circuit lifting. -/

namespace DivisionFree

open PolynomialArithmetic
open scoped BigOperators

universe u

theorem truncatedLiftAux_cost {I O : Type} (q : ℕ) (C : Circuit I O)
    (fO : Fintype O) :
    (truncatedLiftAux.{u} q fO C).cost =
      q * (C.additions + C.negations) + (fastMultiplier.{u} q).cost * C.multiplications := by
  classical
  induction C with
  | wire s => simp [truncatedLiftAux, Circuit.additions, Circuit.negations, Circuit.multiplications]
  | zero => simp [truncatedLiftAux, Circuit.additions, Circuit.negations, Circuit.multiplications]
  | integer z =>
    simp [truncatedLiftAux, Circuit.additions, Circuit.negations, Circuit.multiplications]
  | add =>
    simp [truncatedLiftAux, Circuit.truncatedLift_add_cost,
      Circuit.additions, Circuit.negations, Circuit.multiplications]
  | neg =>
    simp [truncatedLiftAux, Circuit.truncatedLift_neg_cost,
      Circuit.additions, Circuit.negations, Circuit.multiplications]
  | mul =>
    simp [truncatedLiftAux, Circuit.truncatedLift_mul_cost,
      Circuit.additions, Circuit.negations, Circuit.multiplications]
  | comp first second ihf ihs =>
    simp only [truncatedLiftAux, Circuit.comp_cost, ihf, ihs,
      Circuit.additions, Circuit.negations, Circuit.multiplications]
    ring
  | pair left right ihl ihr =>
    simp only [truncatedLiftAux, Circuit.comp_cost, Circuit.pair_cost,
      Circuit.wire_cost, Nat.add_zero, ihl, ihr,
      Circuit.additions, Circuit.negations, Circuit.multiplications]
    ring
  | @bundle I J O inst branches ih =>
    by_cases hj : Nonempty J
    · simp only [truncatedLiftAux, dif_pos hj, Circuit.comp_cost, Circuit.bundle_cost,
        Circuit.wire_cost, Nat.add_zero, ih,
        Circuit.additions, Circuit.negations, Circuit.multiplications,
        Nat.mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    · letI : IsEmpty J := not_nonempty_iff.mp hj
      simp [truncatedLiftAux, hj, Circuit.additions, Circuit.negations, Circuit.multiplications]

theorem truncatedLift_cost {I O : Type} [Fintype O] (q : ℕ) (C : Circuit I O) :
    (truncatedLift.{u} q C).cost =
      q * (C.additions + C.negations) + (fastMultiplier.{u} q).cost * C.multiplications :=
  truncatedLiftAux_cost q C inferInstance

theorem truncatedLift_cost_le {I O : Type} [Fintype O] (q : ℕ) (C : Circuit I O) :
    (truncatedLift.{u} q C).cost ≤ (q + (fastMultiplier.{u} q).cost) * C.cost := by
  rw [truncatedLift_cost, Circuit.cost]
  nlinarith [Nat.zero_le (q*C.multiplications),
    Nat.zero_le ((fastMultiplier.{u} q).cost * (C.additions+C.negations))]

theorem truncatedLiftAux_constantBits {I O : Type} (q : ℕ) (C : Circuit I O)
    (fO : Fintype O) :
    (truncatedLiftAux.{u} q fO C).constantBits = C.constantBits +
      (fastMultiplier.{u} q).circuit.constantBits * C.multiplications := by
  classical
  induction C with
  | wire s => simp [truncatedLiftAux, Circuit.constantBits, Circuit.multiplications]
  | zero => simp [truncatedLiftAux, Circuit.constantBits, Circuit.multiplications]
  | integer z => simp [truncatedLiftAux, Circuit.constantBits, Circuit.multiplications]
  | add =>
    simp [truncatedLiftAux, Circuit.truncatedLiftAdd, Circuit.constantBits, Circuit.multiplications]
  | neg =>
    simp [truncatedLiftAux, Circuit.truncatedLiftNeg, Circuit.constantBits, Circuit.multiplications]
  | mul =>
    simp [truncatedLiftAux, Circuit.truncatedLiftMul, Circuit.constantBits, Circuit.multiplications]
  | comp first second ihf ihs =>
    simp only [truncatedLiftAux, Circuit.comp_constantBits, ihf, ihs,
      Circuit.constantBits, Circuit.multiplications]
    ring
  | pair left right ihl ihr =>
    simp only [truncatedLiftAux, Circuit.comp_constantBits,
      Circuit.constantBits, Nat.add_zero, ihl, ihr, Circuit.multiplications]
    ring
  | @bundle I J O inst branches ih =>
    by_cases hj : Nonempty J
    · simp only [truncatedLiftAux, dif_pos hj, Circuit.comp_constantBits,
        Circuit.constantBits, Nat.add_zero, ih,
        Circuit.multiplications, Finset.sum_add_distrib, Finset.mul_sum]
    · letI : IsEmpty J := not_nonempty_iff.mp hj
      simp [truncatedLiftAux, hj, Circuit.constantBits, Circuit.multiplications]

theorem truncatedLift_constantBits {I O : Type} [Fintype O] (q : ℕ) (C : Circuit I O) :
    (truncatedLift.{u} q C).constantBits = C.constantBits +
      (fastMultiplier.{u} q).circuit.constantBits * C.multiplications :=
  truncatedLiftAux_constantBits q C inferInstance

end DivisionFree
