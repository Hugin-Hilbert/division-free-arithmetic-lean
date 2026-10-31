import DivisionFree.Fourier.PrimePowerMultiplier
import DivisionFree.Fourier.PrimePowerResources

/-!
# Syntactic resources for the binary Cantor--Kaltofen circuit

These bounds concern the circuit actually built by `primePowerCircuit 2`.
In particular, they count the schoolbook leaves and every extension-product
node in that circuit, rather than an abstract multiplier provider.
-/

namespace DivisionFree.Fourier

@[simp] theorem castCyclotomicCircuit_multiplications {m n : ℕ} (h : m = n)
    (P : Circuit (Bool × ZMod m) (ZMod m)) :
    (castCyclotomicCircuit h P).multiplications = P.multiplications := by
  subst n
  rfl

/-- The recursive circuit specialized to powers of two. -/
noncomputable abbrev binaryCantorCircuit (Q : ℕ) :
    Circuit (Bool × ZMod (2 ^ Q)) (ZMod (2 ^ Q)) :=
  primePowerCircuit 2 Q

theorem binaryCantorCircuit_base_cost (Q : ℕ) (hQ : Q ≤ 2) :
    (binaryCantorCircuit Q).cost ≤ 14 * 2 ^ Q := by
  rw [binaryCantorCircuit, primePowerCircuit_base_cost 2 Q hQ]
  have hpow : 2 ^ Q ≤ 4 := by
    calc
      2 ^ Q ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hQ
      _ = 4 := by norm_num
  nlinarith [Nat.one_le_pow Q 2 (by omega : 0 < 2)]

theorem binaryCantorCircuit_base_cost_tight (Q : ℕ) (hQ : Q ≤ 2) :
    (binaryCantorCircuit Q).cost ≤ 8 * 2 ^ Q := by
  rw [binaryCantorCircuit, primePowerCircuit_base_cost 2 Q hQ]
  have hpow : 2 ^ Q ≤ 4 := by
    calc
      2 ^ Q ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hQ
      _ = 4 := by norm_num
  nlinarith [Nat.one_le_pow Q 2 (by omega : 0 < 2)]

theorem binaryCantorCircuit_base_multiplications (Q : ℕ) (hQ : Q ≤ 2) :
    (binaryCantorCircuit Q).multiplications ≤ 9 * 2 ^ Q := by
  have hcost : (binaryCantorCircuit Q).cost = 2 * (2 ^ Q) ^ 2 := by
    rw [binaryCantorCircuit, primePowerCircuit_base_cost 2 Q hQ]
  have hpow : 2 ^ Q ≤ 4 := by
    calc
      2 ^ Q ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hQ
      _ = 4 := by norm_num
  have hsq : (2 ^ Q) ^ 2 ≤ 4 * 2 ^ Q := by
    simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ Q) hpow
  calc
    (binaryCantorCircuit Q).multiplications ≤ (binaryCantorCircuit Q).cost := by
      unfold Circuit.cost
      omega
    _ ≤ 9 * 2 ^ Q := by
      rw [hcost]
      calc
        2 * (2 ^ Q) ^ 2 ≤ 2 * (4 * 2 ^ Q) := Nat.mul_le_mul_left 2 hsq
        _ ≤ 9 * 2 ^ Q := by omega

/-- The schoolbook leaves use exactly one multiplication per coefficient pair. -/
theorem binaryCantorCircuit_base_multiplications_tight (Q : ℕ) (hQ : Q ≤ 2) :
    (binaryCantorCircuit Q).multiplications ≤ 4 * 2 ^ Q := by
  rw [binaryCantorCircuit, primePowerCircuit, dif_pos hQ, cyclicSchoolbook_multiplications_eq]
  have hpow : 2 ^ Q ≤ 4 := by
    calc
      2 ^ Q ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hQ
      _ = 4 := by norm_num
  simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ Q) hpow

theorem binaryCantorCircuit_step_multiplications (Q : ℕ) (hQ : 2 < Q) :
    (binaryCantorCircuit Q).multiplications =
      2 * 2 ^ outerExponent Q *
        (binaryCantorCircuit (innerExponent Q)).multiplications := by
  rw [binaryCantorCircuit, primePowerCircuit, dif_neg (by omega),
    castCyclotomicCircuit_multiplications]
  rw [extensionProduct_multiplications]
  · simp [binaryCantorCircuit, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

theorem binaryCantorCircuit_step_cost_le (Q : ℕ) (hQ : 2 < Q) :
    (binaryCantorCircuit Q).cost ≤
      2 * 2 ^ outerExponent Q *
          (binaryCantorCircuit (innerExponent Q)).cost +
        14 * 2 ^ Q * (Q - 1) := by
  rw [binaryCantorCircuit, primePowerCircuit_step_cost 2 Q hQ]
  have hsum := exponents_sum Q hQ
  have hr := outer_succ_le_inner Q
  have hrf : outerExponent Q + 1 ≤ Q - 1 := by omega
  have hpow : 2 ^ innerExponent Q * 2 ^ (outerExponent Q + 1) = 2 ^ (Q + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow' : 2 ^ (outerExponent Q + 1) * 2 ^ innerExponent Q = 2 ^ (Q + 1) := by
    rw [Nat.mul_comm, hpow]
  have hlarge : 2 ^ (Q + 1) ≤ 4 * 2 ^ Q := by
    rw [pow_succ]
    omega
  have hrec : 2 ^ (outerExponent Q + 1) *
      (primePowerCircuit 2 (innerExponent Q)).cost =
      2 * 2 ^ outerExponent Q *
        (binaryCantorCircuit (innerExponent Q)).cost := by
    simp [binaryCantorCircuit, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
  rw [hrec]
  have hfirst :
      3 * 2 ^ innerExponent Q * 2 * (outerExponent Q + 1) *
          2 ^ (outerExponent Q + 1) =
        12 * 2 ^ Q * (outerExponent Q + 1) := by
    calc
      _ = 6 * (2 ^ innerExponent Q * 2 ^ (outerExponent Q + 1)) *
          (outerExponent Q + 1) := by ring
      _ = 12 * 2 ^ Q * (outerExponent Q + 1) := by rw [hpow]; ring
  have hthird : 2 ^ (outerExponent Q + 1) * 2 ^ innerExponent Q =
      2 * 2 ^ Q := by
    rw [hpow']
    rw [pow_succ]
    ring
  rw [hfirst, hthird]
  have h_overhead :
      12 * 2 ^ Q * (outerExponent Q + 1) + 2 * 2 ^ Q ≤
        14 * 2 ^ Q * (Q - 1) := by
    have houter : 1 ≤ outerExponent Q := one_le_outerExponent Q hQ
    have hlin : 12 * (outerExponent Q + 1) + 2 ≤ 14 * (Q - 1) := by omega
    nlinarith
  nlinarith


/-- Sharper normalized toll, including the worst small recursive exponent. -/
theorem binaryCantorCircuit_step_cost_tight (Q : ℕ) (hQ : 2 < Q) :
    (binaryCantorCircuit Q).cost ≤
      2 * 2 ^ outerExponent Q *
          (binaryCantorCircuit (innerExponent Q)).cost +
        13 * 2 ^ Q * (Q - 1) := by
  rw [binaryCantorCircuit, primePowerCircuit_step_cost 2 Q hQ]
  have hsum := exponents_sum Q hQ
  have hr := outer_succ_le_inner Q
  have hrf : outerExponent Q + 1 ≤ Q - 1 := by omega
  have hpow : 2 ^ innerExponent Q * 2 ^ (outerExponent Q + 1) = 2 ^ (Q + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow' : 2 ^ (outerExponent Q + 1) * 2 ^ innerExponent Q = 2 ^ (Q + 1) := by
    rw [Nat.mul_comm, hpow]
  have hlarge : 2 ^ (Q + 1) ≤ 4 * 2 ^ Q := by
    rw [pow_succ]
    omega
  have hrec : 2 ^ (outerExponent Q + 1) *
      (primePowerCircuit 2 (innerExponent Q)).cost =
      2 * 2 ^ outerExponent Q *
        (binaryCantorCircuit (innerExponent Q)).cost := by
    simp [binaryCantorCircuit, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
  rw [hrec]
  have hfirst :
      3 * 2 ^ innerExponent Q * 2 * (outerExponent Q + 1) *
          2 ^ (outerExponent Q + 1) =
        12 * 2 ^ Q * (outerExponent Q + 1) := by
    calc
      _ = 6 * (2 ^ innerExponent Q * 2 ^ (outerExponent Q + 1)) *
          (outerExponent Q + 1) := by ring
      _ = 12 * 2 ^ Q * (outerExponent Q + 1) := by rw [hpow]; ring
  have hthird : 2 ^ (outerExponent Q + 1) * 2 ^ innerExponent Q =
      2 * 2 ^ Q := by
    rw [hpow']
    rw [pow_succ]
    ring
  rw [hfirst, hthird]
  have h_overhead :
      12 * 2 ^ Q * (outerExponent Q + 1) + 2 * 2 ^ Q ≤
        13 * 2 ^ Q * (Q - 1) := by
    have houter : 1 ≤ outerExponent Q := one_le_outerExponent Q hQ
    have hlin : 12 * (outerExponent Q + 1) + 2 ≤ 13 * (Q - 1) := by omega
    nlinarith
  nlinarith


/-- For exponents at least four, the toll has a smaller uniform coefficient. -/
theorem binaryCantorCircuit_step_cost_large (Q : ℕ) (hQ : 3 < Q) :
    (binaryCantorCircuit Q).cost ≤
      2 * 2 ^ outerExponent Q *
          (binaryCantorCircuit (innerExponent Q)).cost +
        12 * 2 ^ Q * (Q - 1) := by
  have hlargeQ : 2 < Q := by omega
  rw [binaryCantorCircuit, primePowerCircuit_step_cost 2 Q hlargeQ]
  have hsum := exponents_sum Q hlargeQ
  have hr := outer_succ_le_inner Q
  have hrf : outerExponent Q + 1 ≤ Q - 1 := by omega
  have hpow : 2 ^ innerExponent Q * 2 ^ (outerExponent Q + 1) = 2 ^ (Q + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow' : 2 ^ (outerExponent Q + 1) * 2 ^ innerExponent Q = 2 ^ (Q + 1) := by
    rw [Nat.mul_comm, hpow]
  have hlarge : 2 ^ (Q + 1) ≤ 4 * 2 ^ Q := by
    rw [pow_succ]
    omega
  have hrec : 2 ^ (outerExponent Q + 1) *
      (primePowerCircuit 2 (innerExponent Q)).cost =
      2 * 2 ^ outerExponent Q *
        (binaryCantorCircuit (innerExponent Q)).cost := by
    simp [binaryCantorCircuit, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
  rw [hrec]
  have hfirst :
      3 * 2 ^ innerExponent Q * 2 * (outerExponent Q + 1) *
          2 ^ (outerExponent Q + 1) =
        12 * 2 ^ Q * (outerExponent Q + 1) := by
    calc
      _ = 6 * (2 ^ innerExponent Q * 2 ^ (outerExponent Q + 1)) *
          (outerExponent Q + 1) := by ring
      _ = 12 * 2 ^ Q * (outerExponent Q + 1) := by rw [hpow]; ring
  have hthird : 2 ^ (outerExponent Q + 1) * 2 ^ innerExponent Q =
      2 * 2 ^ Q := by
    rw [hpow']
    rw [pow_succ]
    ring
  rw [hfirst, hthird]
  have h_overhead :
      12 * 2 ^ Q * (outerExponent Q + 1) + 2 * 2 ^ Q ≤
        12 * 2 ^ Q * (Q - 1) := by
    have houter : 1 ≤ outerExponent Q := one_le_outerExponent Q hlargeQ
    have hinner : 3 ≤ innerExponent Q := by
      simp only [innerExponent]
      omega
    have hlin : 12 * (outerExponent Q + 1) + 2 ≤ 12 * (Q - 1) := by omega
    nlinarith
  nlinarith



end DivisionFree.Fourier
