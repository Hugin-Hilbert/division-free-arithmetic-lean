import DivisionFree.Constants

/-! Concrete division-free circuits for the powers of a ring input. -/

namespace DivisionFree.Fourier

open DivisionFree

private def powerTableStepBranch (n : ℕ) (i : Fin (n + 2)) :
    Circuit (PUnit ⊕ Fin (n + 1)) PUnit :=
  if hi : i.val ≤ n then
    .wire (fun _ : PUnit => Sum.inr ⟨i.val, by omega⟩)
  else
    .comp
      (.wire (fun b : Bool =>
        if b then Sum.inl PUnit.unit else Sum.inr ⟨n, by omega⟩))
      .mul

/-- Return the table `1, w, ..., w^n` for the input `w`. -/
def powerTable : (n : ℕ) → Circuit PUnit (Fin (n + 1))
  | 0 => .integer 1
  | n + 1 =>
    .comp (.pair (.wire fun _ : PUnit => PUnit.unit) (powerTable n))
      (.comp (.bundle (powerTableStepBranch n))
        (.wire fun i : Fin (n + 2) => (i, PUnit.unit)))

theorem powerTable_eval {R : Type*} [Ring R] (n : ℕ) (x : PUnit → R)
    (i : Fin (n + 1)) :
    (powerTable n).eval x i = x PUnit.unit ^ i.val := by
  induction n with
  | zero => simp [powerTable]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [powerTable, powerTableStepBranch, Circuit.eval_comp, Circuit.eval_bundle, Circuit.eval_wire,
        Circuit.eval_mul]
      rw [ih ⟨n, by omega⟩]
      rw [pow_succ]
    · have hj : j.val ≤ n := by omega
      simp [powerTable, powerTableStepBranch, Circuit.eval_comp, Circuit.eval_bundle, Circuit.eval_wire, hj]
      simpa using ih j

theorem powerTable_cost (n : ℕ) : (powerTable n).cost = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powerTable, Circuit.comp_cost, Circuit.pair_cost, Circuit.wire_cost,
      Circuit.bundle_cost]
    have hsumCircuit : ∑ i : Fin (n + 2), (powerTableStepBranch n i).cost = 1 := by
      rw [Finset.sum_eq_single (Fin.last (n + 1))]
      · simp [powerTableStepBranch, Circuit.cost, Circuit.additions,
          Circuit.negations, Circuit.multiplications]
      · intro i hi hne
        have hiv : i.val ≤ n := by
          have hnlast : i.val ≠ n + 1 := by
            intro heq
            apply hne
            exact Fin.ext heq
          omega
        simp [powerTableStepBranch, hiv, Circuit.cost, Circuit.additions, Circuit.negations]
      · simp
    simp only [Nat.zero_add]
    rw [hsumCircuit, ih]

theorem powerTable_multiplications (n : ℕ) :
    (powerTable n).multiplications = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [powerTable, Circuit.comp_multiplications,
      Circuit.pair_multiplications, Circuit.wire_multiplications,
      Circuit.bundle_multiplications]
    have hsumCircuit : ∑ i : Fin (n + 2), (powerTableStepBranch n i).multiplications = 1 := by
      rw [Finset.sum_eq_single (Fin.last (n + 1))]
      · simp [powerTableStepBranch, Circuit.multiplications, Circuit.comp_multiplications]
      · intro i hi hne
        have hiv : i.val ≤ n := by
          have hnlast : i.val ≠ n + 1 := by
            intro heq
            apply hne
            exact Fin.ext heq
          omega
        simp [powerTableStepBranch, hiv]
      · simp
    simp only [Nat.zero_add]
    rw [hsumCircuit, ih]

theorem powerTable_constantBits (n : ℕ) :
    (powerTable n).constantBits = 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [powerTable, Circuit.constantBits, ih]
    rw [Finset.sum_eq_zero]
    · simp
    · intro i hi
      simp only [powerTableStepBranch]
      split_ifs <;> simp [Circuit.constantBits]

end DivisionFree.Fourier
