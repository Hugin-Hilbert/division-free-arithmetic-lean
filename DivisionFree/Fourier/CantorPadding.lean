import DivisionFree.Fourier.CantorCost
import DivisionFree.Fourier.PrimePowerPadding

/-! Translate Cantor recursion envelopes into bounds in the padded input size. -/

namespace DivisionFree.Fourier

/-- Cost envelope after padding to the least convenient prime-power length,
including the cyclic normalization toll. -/
theorem cantorPaddedCost_le (p n A C : ℕ) (hp₂ : 2 ≤ p) (_hp₃ : p ≤ 3)
    (hn : 1 ≤ n)
    (hC : C ≤ A * p ^ paddedExponent p n * 2 ^ depth (paddedExponent p n) *
      (depth (paddedExponent p n) + 1)) :
    C + 2 * (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤
      (4 * A + 4) * p ^ 2 * n * (Nat.log 2 (2 * n) + 1) *
        (Nat.size (Nat.log 2 (2 * n) + 1) + 1) := by
  let Q := paddedExponent p n
  let L := Nat.log 2 (2 * n) + 1
  have hcap : p ^ Q ≤ 2 * p ^ 2 * n := paddedExponent_total_length hp₂ hn
  have hlog : max 1 (Q - 1) ≤ L := by
    simpa [Q, L] using paddedExponent_logBound hp₂ hn
  have hdepth : depth Q ≤ Nat.size L := by
    exact (depth_le_size_max Q).trans (Nat.size_le_size hlog)
  have hpow₂ : 2 ^ depth Q ≤ 2 * L := by
    calc
      2 ^ depth Q ≤ 2 * max 1 (Q - 1) := depth_pow_two_le Q
      _ ≤ 2 * L := Nat.mul_le_mul_left 2 hlog
  have hdepthSucc : depth Q + 1 ≤ Nat.size L + 1 := Nat.add_le_add_right hdepth 1
  have hbase : A * p ^ Q * 2 ^ depth Q * (depth Q + 1) ≤
      4 * A * p ^ 2 * n * L * (Nat.size L + 1) := by
    calc
      A * p ^ Q * 2 ^ depth Q * (depth Q + 1) ≤
          A * (2 * p ^ 2 * n) * (2 * L) * (Nat.size L + 1) := by
            gcongr
      _ = 4 * A * p ^ 2 * n * L * (Nat.size L + 1) := by ring
  have hnorm : 2 * (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤ 4 * p ^ 2 * n := by
    have hpminus : p - 1 ≤ p := Nat.sub_le p 1
    have hexp : p * p ^ (Nat.log p (2 * n) + 1) = p ^ Q := by
      dsimp [Q, paddedExponent]
      calc
        p * p ^ (Nat.log p (2 * n) + 1) =
            p ^ (Nat.log p (2 * n) + 1) * p := Nat.mul_comm _ _
        _ = p ^ ((Nat.log p (2 * n) + 1) + 1) := (pow_succ p _).symm
        _ = p ^ (Nat.log p (2 * n) + 2) := by congr 1
    calc
      2 * (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤
          2 * p * p ^ (Nat.log p (2 * n) + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hpminus)
      _ = 2 * (p * p ^ (Nat.log p (2 * n) + 1)) := by ring
      _ = 2 * p ^ Q := by rw [hexp]
      _ ≤ 2 * (2 * p ^ 2 * n) := Nat.mul_le_mul_left 2 hcap
      _ = 4 * p ^ 2 * n := by ring
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hfactor : 1 ≤ L * (Nat.size L + 1) := by
    have hs : 1 ≤ Nat.size L + 1 := Nat.le_add_left 1 (Nat.size L)
    simpa using Nat.mul_le_mul hL hs
  have hnorm' : 4 * p ^ 2 * n ≤ 4 * p ^ 2 * n * L * (Nat.size L + 1) := by
    calc
      4 * p ^ 2 * n = 4 * p ^ 2 * n * 1 := by simp
      _ ≤ 4 * p ^ 2 * n * (L * (Nat.size L + 1)) :=
        Nat.mul_le_mul_left (4 * p ^ 2 * n) hfactor
      _ = 4 * p ^ 2 * n * L * (Nat.size L + 1) := by ring
  calc
    C + 2 * (p - 1) * p ^ (Nat.log p (2 * n) + 1) ≤
        4 * A * p ^ 2 * n * L * (Nat.size L + 1) + 4 * p ^ 2 * n :=
      Nat.add_le_add (hC.trans hbase) hnorm
    _ ≤ 4 * A * p ^ 2 * n * L * (Nat.size L + 1) +
        4 * p ^ 2 * n * L * (Nat.size L + 1) := Nat.add_le_add_left hnorm' _
    _ = (4 * A + 4) * p ^ 2 * n * L * (Nat.size L + 1) := by ring

/-- Padding bound retaining the base-specific leaf multiplication count. -/
theorem cantorPaddedMultiplications_general (p n K B : ℕ) (hp₂ : 2 ≤ p)
    (hn : 1 ≤ n)
    (hB : B ≤ K * p ^ paddedExponent p n *
      2 ^ depth (paddedExponent p n)) :
    B ≤ (4 * K * p ^ 2) * n * (Nat.log 2 (2 * n) + 1) := by
  let Q := paddedExponent p n
  let L := Nat.log 2 (2 * n) + 1
  have hcap : p ^ Q ≤ 2 * p ^ 2 * n := paddedExponent_total_length hp₂ hn
  have hlog : max 1 (Q - 1) ≤ L := by
    simpa [Q, L] using paddedExponent_logBound hp₂ hn
  have hpow₂ : 2 ^ depth Q ≤ 2 * L := by
    calc
      2 ^ depth Q ≤ 2 * max 1 (Q - 1) := depth_pow_two_le Q
      _ ≤ 2 * L := Nat.mul_le_mul_left 2 hlog
  calc
    B ≤ K * p ^ Q * 2 ^ depth Q := hB
    _ ≤ K * (2 * p ^ 2 * n) * (2 * L) := by gcongr
    _ = (4 * K * p ^ 2) * n * L := by ring

/-- Multiplication-count envelope after prime-power padding. -/
theorem cantorPaddedMultiplications_le (p n B : ℕ) (hp₂ : 2 ≤ p) (hp₃ : p ≤ 3)
    (hn : 1 ≤ n)
    (hB : B ≤ 9 * p ^ paddedExponent p n *
      2 ^ depth (paddedExponent p n)) :
    B ≤ 324 * n * (Nat.log 2 (2 * n) + 1) := by
  let Q := paddedExponent p n
  let L := Nat.log 2 (2 * n) + 1
  have hcap : p ^ Q ≤ 18 * n := paddedExponent_total_length_small hp₂ hp₃ hn
  have hlog : max 1 (Q - 1) ≤ L := by
    simpa [Q, L] using paddedExponent_logBound hp₂ hn
  have hpow₂ : 2 ^ depth Q ≤ 2 * L := by
    calc
      2 ^ depth Q ≤ 2 * max 1 (Q - 1) := depth_pow_two_le Q
      _ ≤ 2 * L := Nat.mul_le_mul_left 2 hlog
  calc
    B ≤ 9 * p ^ Q * 2 ^ depth Q := hB
    _ ≤ 9 * (18 * n) * (2 * L) := by gcongr
    _ = 324 * n * L := by ring

end DivisionFree.Fourier
