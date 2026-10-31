import DivisionFree.Fourier.Parameters
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Sharp recurrence envelopes for the two-call Cantor-style prime-power
recursion. These statements estimate functions satisfying the displayed
recurrences; they do not make a construction or uniformity claim. -/

namespace DivisionFree.Fourier

/-- Number of binary levels associated with the exponent offset `Q-2`. -/
def depth (Q : ℕ) : ℕ := Nat.size (Q - 2)

/-- Halving a positive integer removes one binary digit. -/
theorem size_half_succ {t : ℕ} (ht : t ≠ 0) :
    Nat.size (t / 2) + 1 = Nat.size t := by
  rw [← Nat.div2_val, ← Nat.size_eq_bits_len, Nat.div2_bits_eq_tail,
    ← Nat.size_eq_bits_len, List.length_tail]
  have hs : 0 < t.bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_pos.mpr (Nat.pos_of_ne_zero ht)
  omega

/-- The recursive inner exponent lowers `depth` by one above the base range. -/
theorem depth_inner_succ (Q : ℕ) (hQ : 2 < Q) :
    depth (innerExponent Q) + 1 = depth Q := by
  rw [depth, inner_sub_two Q hQ, depth]
  exact size_half_succ (by omega)

private theorem depth_zero_of_le_two {Q : ℕ} (hQ : Q ≤ 2) : depth Q = 0 := by
  simp [depth, Nat.sub_eq_zero_of_le hQ]

/-- The binary-depth exponential is bounded by twice the exponent offset. -/
theorem depth_pow_two_le (Q : ℕ) :
    2 ^ depth Q ≤ 2 * max 1 (Q - 1) := by
  by_cases hQ : Q ≤ 2
  · rw [depth_zero_of_le_two hQ]
    have hmax : 1 ≤ max 1 (Q - 1) := Nat.le_max_left _ _
    simp
    omega
  · have hQ' : 2 < Q := by omega
    let t := Q - 2
    have ht : t ≠ 0 := by dsimp [t]; omega
    have hs : 0 < Nat.size (Q - 2) := Nat.size_pos.mpr (by omega)
    have hsize : depth Q - 1 < Nat.size t := by
      simpa [depth, t] using Nat.sub_lt hs (by decide : 0 < 1)
    have hpow : 2 ^ (depth Q - 1) ≤ t := Nat.lt_size.mp hsize
    have hdepth : depth Q = (depth Q - 1) + 1 := by
      change Nat.size (Q - 2) = (Nat.size (Q - 2) - 1) + 1
      omega
    rw [hdepth, pow_succ]
    have htbound : t ≤ max 1 (Q - 1) := by dsimp [t]; omega
    calc
      2 ^ (depth Q - 1) * 2 ≤ t * 2 := Nat.mul_le_mul_right 2 hpow
      _ ≤ max 1 (Q - 1) * 2 := Nat.mul_le_mul_right 2 htbound
      _ = 2 * max 1 (Q - 1) := by ring

/-- The binary depth does not exceed the bit size of the exponent offset. -/
theorem depth_le_size_max (Q : ℕ) :
    depth Q ≤ Nat.size (max 1 (Q - 1)) := by
  apply Nat.size_le_size
  omega

/-- A cost recurrence with two recursive calls has the sharp binary-depth
envelope requested for the Cantor-style split. -/
theorem cantorCost_bound (p : ℕ) (_hp : 2 ≤ p) (_hp3 : p ≤ 3)
    (A : ℕ) (C : ℕ → ℕ)
    (hbase : ∀ Q, Q ≤ 2 → C Q ≤ A * p ^ Q)
    (hstep : ∀ Q, 2 < Q →
      C Q ≤ 2 * p ^ (outerExponent Q) * C (innerExponent Q) +
        A * p ^ Q * (Q - 1)) :
    ∀ Q, C Q ≤ A * p ^ Q * 2 ^ depth Q * (depth Q + 1) := by
  intro Q
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hsmall : Q ≤ 2
      · have hbaseQ := hbase Q hsmall
        have hd : depth Q = 0 := depth_zero_of_le_two hsmall
        rw [hd]
        calc
          C Q ≤ A * p ^ Q := hbaseQ
          _ = A * p ^ Q * 2 ^ 0 * (0 + 1) := by simp
      · have hlarge : 2 < Q := by omega
        let q := innerExponent Q
        let r := outerExponent Q
        have hq_lt : q < Q := innerExponent_lt Q hlarge
        have hqr : q + r = Q := exponents_sum Q hlarge
        have hdepth : depth q + 1 = depth Q := depth_inner_succ Q hlarge
        have hIH := ih q hq_lt
        have hIHq : C q ≤ A * p ^ q * 2 ^ depth q * (depth q + 1) := by
          simpa [q] using hIH
        have hrec := hstep Q hlarge
        have hpowp : p ^ r * p ^ q = p ^ Q := by
          rw [← pow_add, Nat.add_comm r q, hqr]
        have hpow2 : 2 ^ depth q * 2 = 2 ^ depth Q := by
          rw [← hdepth, pow_succ]
        have hrecursive :
            2 * p ^ r * C q ≤ A * p ^ Q * 2 ^ depth Q * depth Q := by
          calc
            2 * p ^ r * C q ≤
                2 * p ^ r * (A * p ^ q * 2 ^ depth q * (depth q + 1)) :=
              Nat.mul_le_mul_left (2 * p ^ r) hIHq
            _ = A * p ^ Q * 2 ^ depth Q * depth Q := by
              calc
                _ = A * (p ^ r * p ^ q) * (2 ^ depth q * 2) * (depth q + 1) := by ring
                _ = A * p ^ Q * 2 ^ depth Q * depth Q := by
                  rw [hpowp, hpow2, hdepth]
        have htollbase : Q - 1 ≤ 2 ^ depth Q := by
          have ht := Nat.lt_size_self (Q - 2)
          dsimp [depth]
          omega
        have htoll : A * p ^ Q * (Q - 1) ≤
            A * p ^ Q * 2 ^ depth Q := Nat.mul_le_mul_left (A * p ^ Q) htollbase
        have htarget :
            A * p ^ Q * 2 ^ depth Q * depth Q +
                A * p ^ Q * 2 ^ depth Q ≤
              A * p ^ Q * 2 ^ depth Q * (depth Q + 1) := by
          exact (show A * p ^ Q * 2 ^ depth Q * depth Q +
              A * p ^ Q * 2 ^ depth Q =
                A * p ^ Q * 2 ^ depth Q * (depth Q + 1) by ring).le
        calc
          C Q ≤ 2 * p ^ r * C q + A * p ^ Q * (Q - 1) := by
            simpa [q, r] using hrec
          _ ≤ A * p ^ Q * 2 ^ depth Q * depth Q +
                A * p ^ Q * 2 ^ depth Q := Nat.add_le_add hrecursive htoll
          _ ≤ A * p ^ Q * 2 ^ depth Q * (depth Q + 1) := by
            calc
              _ = A * p ^ Q * 2 ^ depth Q * depth Q +
                  A * p ^ Q * 2 ^ depth Q := by ring
              _ ≤ A * p ^ Q * 2 ^ depth Q * (depth Q + 1) := htarget

/-- Multiplication counts obey the same two-call recursion without a toll. -/
theorem cantorMultiplications_bound_general (K p : ℕ) (_hp : 2 ≤ p) (_hp3 : p ≤ 3)
    (B : ℕ → ℕ)
    (hbase : ∀ Q, Q ≤ 2 → B Q ≤ K * p ^ Q)
    (hstep : ∀ Q, 2 < Q →
      B Q ≤ 2 * p ^ (outerExponent Q) * B (innerExponent Q)) :
    ∀ Q, B Q ≤ K * p ^ Q * 2 ^ depth Q := by
  intro Q
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hsmall : Q ≤ 2
      · have hbaseQ := hbase Q hsmall
        have hd : depth Q = 0 := depth_zero_of_le_two hsmall
        rw [hd]
        calc
          B Q ≤ K * p ^ Q := hbaseQ
          _ = K * p ^ Q * 2 ^ 0 := by simp
      · have hlarge : 2 < Q := by omega
        let q := innerExponent Q
        let r := outerExponent Q
        have hq_lt : q < Q := innerExponent_lt Q hlarge
        have hqr : q + r = Q := exponents_sum Q hlarge
        have hdepth : depth q + 1 = depth Q := depth_inner_succ Q hlarge
        have hIH := ih q hq_lt
        have hIHq : B q ≤ K * p ^ q * 2 ^ depth q := by simpa [q] using hIH
        have hrec := hstep Q hlarge
        have hpowp : p ^ r * p ^ q = p ^ Q := by
          rw [← pow_add, Nat.add_comm r q, hqr]
        have hpow2 : 2 ^ depth q * 2 = 2 ^ depth Q := by
          rw [← hdepth, pow_succ]
        calc
          B Q ≤ 2 * p ^ r * B q := by simpa [q, r] using hrec
          _ ≤ 2 * p ^ r * (K * p ^ q * 2 ^ depth q) :=
            Nat.mul_le_mul_left (2 * p ^ r) hIHq
          _ = K * p ^ Q * 2 ^ depth Q := by
            calc
              _ = K * (p ^ r * p ^ q) * (2 ^ depth q * 2) := by ring
              _ = K * p ^ Q * 2 ^ depth Q := by rw [hpowp, hpow2]


theorem cantorMultiplications_bound (p : ℕ) (_hp : 2 ≤ p) (_hp3 : p ≤ 3)
    (B : ℕ → ℕ)
    (hbase : ∀ Q, Q ≤ 2 → B Q ≤ 9 * p ^ Q)
    (hstep : ∀ Q, 2 < Q →
      B Q ≤ 2 * p ^ (outerExponent Q) * B (innerExponent Q)) :
    ∀ Q, B Q ≤ 9 * p ^ Q * 2 ^ depth Q := by
  intro Q
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      by_cases hsmall : Q ≤ 2
      · have hbaseQ := hbase Q hsmall
        have hd : depth Q = 0 := depth_zero_of_le_two hsmall
        rw [hd]
        calc
          B Q ≤ 9 * p ^ Q := hbaseQ
          _ = 9 * p ^ Q * 2 ^ 0 := by simp
      · have hlarge : 2 < Q := by omega
        let q := innerExponent Q
        let r := outerExponent Q
        have hq_lt : q < Q := innerExponent_lt Q hlarge
        have hqr : q + r = Q := exponents_sum Q hlarge
        have hdepth : depth q + 1 = depth Q := depth_inner_succ Q hlarge
        have hIH := ih q hq_lt
        have hIHq : B q ≤ 9 * p ^ q * 2 ^ depth q := by simpa [q] using hIH
        have hrec := hstep Q hlarge
        have hpowp : p ^ r * p ^ q = p ^ Q := by
          rw [← pow_add, Nat.add_comm r q, hqr]
        have hpow2 : 2 ^ depth q * 2 = 2 ^ depth Q := by
          rw [← hdepth, pow_succ]
        calc
          B Q ≤ 2 * p ^ r * B q := by simpa [q, r] using hrec
          _ ≤ 2 * p ^ r * (9 * p ^ q * 2 ^ depth q) :=
            Nat.mul_le_mul_left (2 * p ^ r) hIHq
          _ = 9 * p ^ Q * 2 ^ depth Q := by
            calc
              _ = 9 * (p ^ r * p ^ q) * (2 ^ depth q * 2) := by ring
              _ = 9 * p ^ Q * 2 ^ depth Q := by rw [hpowp, hpow2]

end DivisionFree.Fourier
