import DivisionFree.Fourier.CyclotomicMultiplier
import DivisionFree.Fourier.PrimePowerCost

/-! A closed recursive, division-free cyclotomic multiplication circuit.
All recursive calls reduce the extension exponent. -/

namespace DivisionFree.Fourier

universe u

/-- Exponent of the prime scaling factor left by unnormalized transforms. -/
def primePowerScale (Q : ℕ) : ℕ :=
  if h : Q ≤ 2 then 0
  else primePowerScale (innerExponent Q) + outerExponent Q + 1
termination_by Q
decreasing_by exact innerExponent_lt Q (by omega)

/-- Actual base-ring circuit: small cyclic schoolbook products at the leaves,
with coefficient regrouping and additive Fourier transforms at every node. -/
noncomputable def primePowerCircuit (p : ℕ) [NeZero p] (Q : ℕ) :
    Circuit (Bool × ZMod (p ^ Q)) (ZMod (p ^ Q)) :=
  if h : Q ≤ 2 then cyclicSchoolbook (p ^ Q)
  else castCyclotomicCircuit (split_powers_mul p Q (by omega))
    (extensionProduct (p ^ innerExponent Q) (p ^ outerExponent Q)
      p (NeZero.pos p) (outerExponent Q + 1) (primePowerCircuit p (innerExponent Q)))
termination_by Q
decreasing_by exact innerExponent_lt Q (by omega)

theorem primePowerScale_le (Q : ℕ) : primePowerScale Q ≤ 2 * Q := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    rw [primePowerScale]
    split_ifs with hsmall
    · omega
    · have hlarge : 2 < Q := by omega
      have hrec := ih (innerExponent Q) (innerExponent_lt Q hlarge)
      have hsum := exponents_sum Q hlarge
      have houter := one_le_outerExponent Q hlarge
      omega

/-- Unconditional correctness over every commutative base ring, including
the zero ring and rings in which the prime or transform length vanishes. -/
theorem primePowerCircuit_correct (p : ℕ) [NeZero p] (hp : p.Prime) (Q : ℕ) :
    CyclotomicCorrect.{u} (p ^ Q) (p ^ primePowerScale Q) (primePowerCircuit p Q) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    by_cases hsmall : Q ≤ 2
    · rw [primePowerCircuit, dif_pos hsmall, primePowerScale, dif_pos hsmall, pow_zero]
      exact cyclicSchoolbook_cyclotomicCorrect (p ^ Q)
    · have hlarge : 2 < Q := by omega
      have hq := two_le_innerExponent Q hlarge
      have hrec := ih (innerExponent Q) (innerExponent_lt Q hlarge)
      rw [primePowerCircuit, dif_neg hsmall, primePowerScale, dif_neg hsmall]
      have hpow : p ^ (primePowerScale (innerExponent Q) + outerExponent Q + 1) =
          p ^ primePowerScale (innerExponent Q) * p ^ (outerExponent Q + 1) := by
        rw [Nat.add_assoc, pow_add]
      rw [hpow]
      apply castCyclotomicCircuit_correct
      exact extensionProduct_primePower_correct p (innerExponent Q) (outerExponent Q)
        hp (by omega) (outer_succ_le_inner Q) _ _ hrec

theorem primePowerCircuit_base_cost (p : ℕ) [NeZero p] (Q : ℕ) (hQ : Q ≤ 2) :
    (primePowerCircuit p Q).cost = 2 * (p ^ Q) ^ 2 := by
  rw [primePowerCircuit, dif_pos hQ, cyclicSchoolbook_cost]

theorem primePowerCircuit_step_cost (p : ℕ) [NeZero p] (Q : ℕ) (hQ : 2 < Q) :
    (primePowerCircuit p Q).cost =
      3 * p ^ innerExponent Q * p * (outerExponent Q + 1) *
        p ^ (outerExponent Q + 1) +
      p ^ (outerExponent Q + 1) * (primePowerCircuit p (innerExponent Q)).cost +
      p ^ (outerExponent Q + 1) * p ^ innerExponent Q := by
  rw [primePowerCircuit, dif_neg (by omega), castCyclotomicCircuit_cost,
    extensionProduct_cost]

/-- The syntactic gate count is quasi-linear in the represented length `p^Q`.
This bound is for the constructed circuit, with no multiplier provider. -/
theorem primePowerCircuit_cost_le (p : ℕ) [NeZero p]
    (hp : 2 ≤ p) (hp3 : p ≤ 3) (Q : ℕ) :
    (primePowerCircuit p Q).cost ≤ 30 * p ^ Q * (max 1 (Q - 1)) ^ 3 := by
  apply primePowerCost_bound p hp hp3 (fun Q => (primePowerCircuit p Q).cost)
  · intro Q hQ
    exact (primePowerCircuit_base_cost p Q hQ).le
  · intro Q hQ
    exact (primePowerCircuit_step_cost p Q hQ).le

end DivisionFree.Fourier
