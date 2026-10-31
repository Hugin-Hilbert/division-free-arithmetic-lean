import DivisionFree.Fourier.CyclotomicMultiplier
import DivisionFree.Fourier.TernaryExtension
import DivisionFree.Fourier.PrimePowerMultiplier
import DivisionFree.Fourier.PrimePowerResources
import DivisionFree.Fourier.BinaryCantorResources

/-! A closed recursive ternary cyclotomic multiplication circuit. -/

namespace DivisionFree.Fourier

universe u

/-- Recursive ternary circuit, with schoolbook multiplication at exponents at
most two. -/
noncomputable def ternaryCircuit (Q : ℕ) :
    Circuit (Bool × ZMod (3 ^ Q)) (ZMod (3 ^ Q)) :=
  if h : Q ≤ 2 then cyclicSchoolbook (3 ^ Q)
  else castCyclotomicCircuit (split_powers_mul 3 Q (by omega))
    (ternaryExtensionProduct (3 ^ innerExponent Q) (outerExponent Q)
      (((3 ^ (innerExponent Q - (outerExponent Q + 1)) : ℕ) : ZMod (3 ^ innerExponent Q)))
      (ternaryCircuit (innerExponent Q)))
termination_by Q
decreasing_by exact innerExponent_lt Q (by omega)

theorem ternaryCircuit_correct (Q : ℕ) :
    CyclotomicCorrect.{u} (3 ^ Q) (3 ^ primePowerScale Q) (ternaryCircuit Q) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    by_cases hsmall : Q ≤ 2
    · rw [ternaryCircuit, dif_pos hsmall, primePowerScale, dif_pos hsmall, pow_zero]
      exact cyclicSchoolbook_cyclotomicCorrect (3 ^ Q)
    · have hlarge : 2 < Q := by omega
      have hqpos : 0 < innerExponent Q := by
        have := two_le_innerExponent Q hlarge
        omega
      have hrec := ih (innerExponent Q) (innerExponent_lt Q hlarge)
      rw [ternaryCircuit, dif_neg hsmall, primePowerScale, dif_neg hsmall]
      have hpow : 3 ^ (primePowerScale (innerExponent Q) + outerExponent Q + 1) =
          3 ^ primePowerScale (innerExponent Q) * 3 ^ (outerExponent Q + 1) := by
        rw [Nat.add_assoc, pow_add]
      rw [hpow]
      apply castCyclotomicCircuit_correct
      exact ternaryExtensionProduct_primePower_correct (innerExponent Q) (outerExponent Q)
        hqpos (outer_succ_le_inner Q) (3 ^ primePowerScale (innerExponent Q))
        (ternaryCircuit (innerExponent Q)) hrec

theorem ternaryCircuit_base_cost (Q : ℕ) (hQ : Q ≤ 2) :
    (ternaryCircuit Q).cost = 2 * (3 ^ Q) ^ 2 := by
  rw [ternaryCircuit, dif_pos hQ, cyclicSchoolbook_cost]

theorem ternaryCircuit_base_cost_le (Q : ℕ) (hQ : Q ≤ 2) :
    (ternaryCircuit Q).cost ≤ 18 * 3 ^ Q := by
  rw [ternaryCircuit_base_cost Q hQ]
  have hpow : 3 ^ Q ≤ 9 := by
    calc
      3 ^ Q ≤ 3 ^ 2 := Nat.pow_le_pow_right (by omega) hQ
      _ = 9 := by norm_num
  nlinarith [Nat.one_le_pow Q 3 (by omega : 0 < 3)]

private theorem sumList_multiplications_eq_length {I : Type}
    (ps : List (Circuit I PUnit)) (h : ∀ p ∈ ps, p.multiplications = 1) :
    (Circuit.sumList ps).multiplications = ps.length := by
  induction ps with
  | nil => simp [Circuit.sumList]
  | cons p ps ih =>
      have hp := h p (by simp)
      have hps : ∀ q ∈ ps, q.multiplications = 1 := by
        intro q hq
        exact h q (by simp [hq])
      simp [Circuit.sumList, hp, ih hps]
      omega

private def ternarySchoolbookTerm (M : ℕ) (k j : ZMod M) :
    Circuit (Bool × ZMod M) PUnit :=
  .comp (.wire fun b : Bool => if b then (true, k - j) else (false, j)) .mul

private theorem cyclicSchoolbook_multiplications (M : ℕ) [NeZero M] :
    (cyclicSchoolbook M).multiplications = M ^ 2 := by
  classical
  unfold cyclicSchoolbook
  change (∑ k : ZMod M,
      (Circuit.sumList (Finset.univ.toList.map (ternarySchoolbookTerm M k))).multiplications) = M ^ 2
  calc
    ∑ k : ZMod M,
        (Circuit.sumList (Finset.univ.toList.map (ternarySchoolbookTerm M k))).multiplications =
        ∑ _k : ZMod M, M := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [sumList_multiplications_eq_length]
          · simp [ZMod.card]
          · intro p hp
            rcases List.mem_map.mp hp with ⟨j, hj, rfl⟩
            simp [ternarySchoolbookTerm]
    _ = M ^ 2 := by simp [ZMod.card, pow_two]

theorem ternaryCircuit_base_multiplications (Q : ℕ) (hQ : Q ≤ 2) :
    (ternaryCircuit Q).multiplications = (3 ^ Q) ^ 2 := by
  rw [ternaryCircuit, dif_pos hQ, cyclicSchoolbook_multiplications]

theorem ternaryCircuit_base_multiplications_le (Q : ℕ) (hQ : Q ≤ 2) :
    (ternaryCircuit Q).multiplications ≤ 9 * 3 ^ Q := by
  rw [ternaryCircuit_base_multiplications Q hQ]
  have hpow : 3 ^ Q ≤ 9 := by
    calc
      3 ^ Q ≤ 3 ^ 2 := Nat.pow_le_pow_right (by omega) hQ
      _ = 9 := by norm_num
  nlinarith [Nat.one_le_pow Q 3 (by omega : 0 < 3)]

theorem ternaryCircuit_step_cost (Q : ℕ) (hQ : 2 < Q) :
    (ternaryCircuit Q).cost =
      18 * 3 ^ innerExponent Q * outerExponent Q * 3 ^ outerExponent Q +
        2 * 3 ^ outerExponent Q * (ternaryCircuit (innerExponent Q)).cost +
        10 * 3 ^ innerExponent Q * 3 ^ outerExponent Q := by
  rw [ternaryCircuit, dif_neg (by omega), castCyclotomicCircuit_cost,
    ternaryExtensionProduct_cost]

theorem ternaryCircuit_step_cost_le (Q : ℕ) (hQ : 2 < Q) :
    (ternaryCircuit Q).cost ≤
      2 * 3 ^ outerExponent Q * (ternaryCircuit (innerExponent Q)).cost +
        18 * 3 ^ Q * (Q - 1) := by
  rw [ternaryCircuit_step_cost Q hQ]
  have hsum := exponents_sum Q hQ
  have hpow : 3 ^ innerExponent Q * 3 ^ outerExponent Q = 3 ^ Q := by
    rw [← pow_add, hsum]
  have hq : 2 ≤ innerExponent Q := two_le_innerExponent Q hQ
  have hcore : 18 * outerExponent Q + 10 ≤ 18 * (Q - 1) := by omega
  calc
    _ = 2 * 3 ^ outerExponent Q * (ternaryCircuit (innerExponent Q)).cost +
        3 ^ innerExponent Q * 3 ^ outerExponent Q *
          (18 * outerExponent Q + 10) := by ring
    _ ≤ 2 * 3 ^ outerExponent Q * (ternaryCircuit (innerExponent Q)).cost +
        3 ^ innerExponent Q * 3 ^ outerExponent Q * (18 * (Q - 1)) := by
          exact Nat.add_le_add_left
            (Nat.mul_le_mul_left _ hcore) _
    _ = _ := by rw [hpow]; ring

theorem ternaryCircuit_step_multiplications (Q : ℕ) (hQ : 2 < Q) :
    (ternaryCircuit Q).multiplications =
      2 * 3 ^ outerExponent Q * (ternaryCircuit (innerExponent Q)).multiplications := by
  rw [ternaryCircuit, dif_neg (by omega), castCyclotomicCircuit_multiplications,
    ternaryExtensionProduct_multiplications]

theorem ternaryCircuit_constantBits (Q : ℕ) :
    (ternaryCircuit Q).constantBits = 0 := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    by_cases hQ : Q ≤ 2
    · rw [ternaryCircuit, dif_pos hQ]
      exact cyclicSchoolbook_constantBits _
    · rw [ternaryCircuit, dif_neg hQ, castCyclotomicCircuit_constantBits,
        ternaryExtensionProduct_constantBits]
      have hlarge : 2 < Q := by omega
      have hrec := ih (innerExponent Q) (innerExponent_lt Q hlarge)
      simp [hrec]

/-- The ternary circuit costs at most the prime-power circuit at the same exponent. -/
theorem ternaryCircuit_cost_le_old (Q : ℕ) :
    (ternaryCircuit Q).cost ≤ (primePowerCircuit 3 Q).cost := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    by_cases hQ : Q ≤ 2
    · rw [ternaryCircuit_base_cost Q hQ, primePowerCircuit_base_cost 3 Q hQ]
    · have hlarge : 2 < Q := by omega
      have hrec := ih (innerExponent Q) (innerExponent_lt Q hlarge)
      rw [ternaryCircuit_step_cost Q hlarge, primePowerCircuit_step_cost 3 Q hlarge]
      let B := 3 ^ outerExponent Q
      have hrec' : 2 * B * (ternaryCircuit (innerExponent Q)).cost ≤
          3 * B * (primePowerCircuit 3 (innerExponent Q)).cost := by
        have hmul := Nat.mul_le_mul_left (2 * B) hrec
        nlinarith [Nat.zero_le (B * (primePowerCircuit 3 (innerExponent Q)).cost)]
      rw [pow_succ]
      dsimp [B] at hrec'
      nlinarith [hrec', Nat.zero_le (3 ^ innerExponent Q * 3 ^ outerExponent Q),
        Nat.zero_le (3 ^ innerExponent Q * 3 ^ outerExponent Q * outerExponent Q)]

end DivisionFree.Fourier
