import DivisionFree.Fourier.PrimePowerMultiplier
import DivisionFree.Fourier.CyclicProductResources

/-!
# Constant-size resources in recursive prime-power circuits
-/

namespace DivisionFree.Fourier

@[simp] theorem castCyclotomicCircuit_constantBits {m n : ℕ} (h : m = n)
    (P : Circuit (Bool × ZMod m) (ZMod m)) :
    (castCyclotomicCircuit h P).constantBits = P.constantBits := by
  subst n
  rfl

theorem primePowerCircuit_constantBits (p : ℕ) [NeZero p] (Q : ℕ) :
    (primePowerCircuit p Q).constantBits = 0 := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
    by_cases hsmall : Q ≤ 2
    · rw [primePowerCircuit, dif_pos hsmall]
      exact cyclicSchoolbook_constantBits (p ^ Q)
    · have hlarge : 2 < Q := by omega
      have hrec := ih (innerExponent Q) (innerExponent_lt Q hlarge)
      rw [primePowerCircuit, dif_neg hsmall, castCyclotomicCircuit_constantBits]
      rw [extensionProduct_constantBits]
      simp [hrec]

end DivisionFree.Fourier
