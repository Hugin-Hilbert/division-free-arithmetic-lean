import DivisionFree.Fourier.Parameters
import Mathlib.Tactic

/-! Numerical upper bound for the stated prime-power recursive cost recurrence.
This is only a recurrence estimate; it makes no algorithm claim. -/

namespace DivisionFree.Fourier

private theorem cubicSplit_step (t : ℕ) (ht : 1 ≤ t) :
    3 * (t / 2 + 1) ^ 3 + (t + 1) ≤ (t + 1) ^ 3 := by
  have hdiv : t = 2 * (t / 2) + t % 2 := by omega
  have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · rw [hmod] at hdiv
    rw [hdiv]
    have hquot : (2 * (t / 2) + 0) / 2 = t / 2 := by omega
    rw [hquot]
    have hqpos : 1 ≤ t / 2 := by omega
    nlinarith [sq_nonneg (t / 2 : ℕ),
      mul_nonneg (show 0 ≤ (t / 2 : ℕ) - 1 by omega)
        (show 0 ≤ 5 * (t / 2 : ℕ) ^ 2 + 8 * (t / 2 : ℕ) + 3 by positivity)]
  · rw [hmod] at hdiv
    rw [hdiv]
    have hquot : (2 * (t / 2) + 1) / 2 = t / 2 := by omega
    rw [hquot]
    have hq : 0 ≤ (t / 2 : ℕ) := Nat.zero_le _
    nlinarith [sq_nonneg (t / 2 : ℕ),
      mul_nonneg hq (sq_nonneg (t / 2 : ℕ)),
      mul_nonneg hq (sq_nonneg ((t / 2 : ℕ) + 1))]

/-- If the base cases are quadratic and each recursive step obeys the stated
prime-power recurrence, the cost is bounded by `30 p^Q (Q-1)^3` for `Q>2`
and by the corresponding max-normalized expression for every `Q`. -/
theorem primePowerCost_bound (p : ℕ) (hp : 2 ≤ p) (hp3 : p ≤ 3)
    (C : ℕ → ℕ)
    (hbase : ∀ Q, Q ≤ 2 → C Q ≤ 2 * (p ^ Q) ^ 2)
    (hstep : ∀ Q, 2 < Q →
      C Q ≤
        3 * p ^ innerExponent Q * p * (outerExponent Q + 1) *
            p ^ (outerExponent Q + 1) +
          p ^ (outerExponent Q + 1) * C (innerExponent Q) +
          p ^ (outerExponent Q + 1) * p ^ innerExponent Q) :
    ∀ Q, C Q ≤ 30 * p ^ Q * (max 1 (Q - 1)) ^ 3 := by
  intro Q
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hsmall : Q ≤ 2
      · have hpQ : p ^ Q ≤ 9 := by
          have hpq : p ^ Q ≤ p ^ 2 := Nat.pow_le_pow_right (by omega : 0 < p) hsmall
          have hp2 : p ^ 2 ≤ 9 := by nlinarith
          omega
        have hmax : 1 ≤ max 1 (Q - 1) := Nat.le_max_left _ _
        have hbaseQ := hbase Q hsmall
        have hpow : (p ^ Q) ^ 2 ≤ 9 * p ^ Q := by
          simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left (p ^ Q) hpQ
        calc
          C Q ≤ 2 * (p ^ Q) ^ 2 := hbaseQ
          _ ≤ 18 * p ^ Q := by
            calc
              2 * (p ^ Q) ^ 2 ≤ 2 * (9 * p ^ Q) := Nat.mul_le_mul_left 2 hpow
              _ = 18 * p ^ Q := by ring
          _ ≤ 30 * p ^ Q * (max 1 (Q - 1)) ^ 3 := by
            have hpQpos : 1 ≤ p ^ Q := Nat.one_le_pow Q p (by omega)
            have hcube : 1 ≤ (max 1 (Q - 1)) ^ 3 := Nat.one_le_pow 3 _ hmax
            nlinarith
      · have hlarge : 2 < Q := by omega
        let q := innerExponent Q
        let r := outerExponent Q
        have hq : 2 ≤ q := two_le_innerExponent Q hlarge
        have hq_lt : q < Q := innerExponent_lt Q hlarge
        have hqr : q + r = Q := exponents_sum Q hlarge
        have hr1 : r + 1 ≤ q := outer_succ_le_inner Q
        have hrQ : r + 1 ≤ Q - 1 := by omega
        have hsub : q - 2 = (Q - 2) / 2 := by
          dsimp [q]
          exact inner_sub_two Q hlarge
        have hsub' : q - 1 = (Q - 2) / 2 + 1 := by omega
        have hIH := ih q hq_lt
        have hIHq : C q ≤ 30 * p ^ q * (q - 1) ^ 3 := by
          have hqmax : max 1 (q - 1) = q - 1 := by omega
          simpa [q, hqmax] using hIH
        have hpow : p ^ q * p ^ (r + 1) = p ^ (Q + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hpow' : p ^ q * p * p ^ (r + 1) = p ^ (Q + 2) := by
          rw [← pow_succ, ← pow_add]
          congr 1
          omega
        have hpowRec : p ^ (r + 1) * p ^ q = p ^ (Q + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hp2 : p ^ 2 ≤ 9 := by nlinarith
        have hcore :
            30 * p * (q - 1) ^ 3 + 3 * p ^ 2 * (r + 1) + p ≤
              30 * (Q - 1) ^ 3 := by
          have hsmallCube : (q - 1) ^ 3 ≤ ((Q - 2) / 2 + 1) ^ 3 := by
            rw [hsub']
          have hterm1 : p * (q - 1) ^ 3 ≤ 3 * ((Q - 2) / 2 + 1) ^ 3 :=
            Nat.mul_le_mul (by omega) hsmallCube
          have hterm2 : p ^ 2 * (r + 1) ≤ 9 * (Q - 1) :=
            Nat.mul_le_mul hp2 hrQ
          have hlin : 27 * (Q - 1) + 3 ≤ 30 * (Q - 1) := by omega
          have hsplit := cubicSplit_step (Q - 2) (by omega)
          have hsplit' :
              90 * ((Q - 2) / 2 + 1) ^ 3 + 30 * (Q - 1) ≤
                30 * (Q - 1) ^ 3 := by
            have hm := Nat.mul_le_mul_left 30 hsplit
            have hidx : Q - 2 + 1 = Q - 1 := by omega
            rw [hidx] at hm
            nlinarith [hm]
          nlinarith [hterm1, hterm2, hlin, hsplit']
        have hrec := hstep Q hlarge
        have hrec' : C Q ≤ p ^ Q *
            (30 * p * (q - 1) ^ 3 + 3 * p ^ 2 * (r + 1) + p) := by
          have hfirst :
              3 * p ^ q * p * (r + 1) * p ^ (r + 1) =
                3 * p ^ (Q + 2) * (r + 1) := by
            calc
              _ = 3 * (p ^ q * p * p ^ (r + 1)) * (r + 1) := by ring
              _ = 3 * p ^ (Q + 2) * (r + 1) := by rw [hpow']
          have hQpow1 : p ^ (Q + 1) = p ^ Q * p := by
            rw [pow_add]
            simp
          have hQpow2 : p ^ (Q + 2) = p ^ Q * p ^ 2 := by
            rw [pow_add]
          calc
            C Q ≤ 3 * p ^ q * p * (r + 1) * p ^ (r + 1) +
                p ^ (r + 1) * C q + p ^ (r + 1) * p ^ q := by
              simpa [q, r] using hrec
            _ ≤ 3 * p ^ (Q + 2) * (r + 1) +
                p ^ (r + 1) * (30 * p ^ q * (q - 1) ^ 3) +
                p ^ (r + 1) * p ^ q := by
              apply Nat.add_le_add
              · apply Nat.add_le_add
                · rw [hfirst]
                · exact Nat.mul_le_mul_left (p ^ (r + 1)) hIHq
              · exact le_rfl
            _ = p ^ Q *
                (30 * p * (q - 1) ^ 3 + 3 * p ^ 2 * (r + 1) + p) := by
              calc
                _ = 3 * (p ^ Q * p ^ 2) * (r + 1) +
                    30 * (p ^ q * p ^ (r + 1)) * (q - 1) ^ 3 +
                    p ^ (r + 1) * p ^ q := by rw [hQpow2]; ring
                _ = p ^ Q *
                    (30 * p * (q - 1) ^ 3 + 3 * p ^ 2 * (r + 1) + p) := by
                  rw [hpow, hpowRec]
                  ring
        have htarget :
            p ^ Q * (30 * p * (q - 1) ^ 3 + 3 * p ^ 2 * (r + 1) + p) ≤
              30 * p ^ Q * (max 1 (Q - 1)) ^ 3 := by
          have hmax : max 1 (Q - 1) = Q - 1 := by omega
          rw [hmax]
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
            Nat.mul_le_mul_left (p ^ Q) hcore
        exact hrec'.trans htarget

end DivisionFree.Fourier
