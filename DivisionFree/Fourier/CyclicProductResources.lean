import DivisionFree.Fourier.ExtensionProduct
import DivisionFree.Fourier.CoefficientSplit
import DivisionFree.Fourier.CoefficientRecombine

/-!
# Gate resource recurrences for Fourier products
-/

namespace DivisionFree.Fourier

open DivisionFree

variable (M : ℕ) [NeZero M]

theorem cyclicProduct_multiplications (s : ℕ) (hs : 0 < s) (r : ℕ)
    [NeZero (s ^ r)] (e : ZMod M) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (cyclicProduct M s hs r e P).multiplications = s ^ r * P.multiplications := by
  classical
  simp [cyclicProduct, forwardPair, pointwise, Circuit.multiplications,
    cyclicRadix_multiplications]

theorem cyclicProduct_constantBits (s : ℕ) (hs : 0 < s) (r : ℕ)
    [NeZero (s ^ r)] (e : ZMod M) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (cyclicProduct M s hs r e P).constantBits = s ^ r * P.constantBits := by
  classical
  simp [cyclicProduct, forwardPair, pointwise, Circuit.constantBits,
    cyclicRadix_constantBits]

variable (m n : ℕ) [NeZero m] [NeZero n]

theorem splitInput_multiplications (L : ℕ) :
    (splitInput m n L).multiplications = 0 := by
  classical
  simp only [splitInput, Circuit.comp_multiplications, Circuit.bundle_multiplications]
  apply Finset.sum_eq_zero
  intro o ho
  by_cases h : o.2.1.val < n <;> simp [h]


theorem extensionProduct_multiplications (s : ℕ) (hs : 0 < s) (r : ℕ)
    [NeZero (s ^ r)] (P : Circuit (Bool × ZMod m) (ZMod m)) :
    (extensionProduct m n s hs r P).multiplications = s ^ r * P.multiplications := by
  classical
  simp [extensionProduct, splitInput_multiplications,
    coefficientRecombine_multiplications, cyclicProduct_multiplications,
    Circuit.multiplications]

theorem extensionProduct_constantBits (s : ℕ) (hs : 0 < s) (r : ℕ)
    [NeZero (s ^ r)] (P : Circuit (Bool × ZMod m) (ZMod m)) :
    (extensionProduct m n s hs r P).constantBits = s ^ r * P.constantBits := by
  classical
  simp [extensionProduct, splitInput_constantBits,
    coefficientRecombine_constantBits, cyclicProduct_constantBits,
    Circuit.constantBits]

end DivisionFree.Fourier
