import DivisionFree.Fourier.CyclotomicTower

/-! A tower map with dimensions in product form, for coefficient regrouping. -/

namespace DivisionFree.Fourier

open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem cyclotomicSplit_relation (p q r : ℕ) (hp : p.Prime) (hq : 0 < q) :
    (Polynomial.cyclotomic (p ^ q) R).eval₂
      (AdjoinRoot.of (Polynomial.cyclotomic (p ^ q * p ^ r) R))
      (cyclotomicRoot R (p ^ q * p ^ r) ^ (p ^ r)) = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have he : p ^ (t + 1) * p ^ r = p ^ (t + r + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [he]
  exact cyclotomicTower_relation p t r hp

/-- Map the smaller cyclotomic extension into the larger one by sending its
root to the stride power of the larger root. -/
noncomputable def cyclotomicSplitMap (p q r : ℕ) (hp : p.Prime) (hq : 0 < q) :
    CyclotomicRing R (p ^ q) →+* CyclotomicRing R (p ^ q * p ^ r) :=
  AdjoinRoot.lift (AdjoinRoot.of _) (cyclotomicRoot R (p ^ q * p ^ r) ^ (p ^ r))
    (cyclotomicSplit_relation p q r hp hq)

@[simp] theorem cyclotomicSplitMap_root (p q r : ℕ) (hp : p.Prime) (hq : 0 < q) :
    cyclotomicSplitMap (R := R) p q r hp hq (cyclotomicRoot R (p ^ q)) =
      cyclotomicRoot R (p ^ q * p ^ r) ^ (p ^ r) := by
  simp [cyclotomicSplitMap, cyclotomicRoot]

@[simp] theorem cyclotomicSplitMap_of (p q r : ℕ) (hp : p.Prime) (hq : 0 < q)
    (a : R) :
    cyclotomicSplitMap (R := R) p q r hp hq (AdjoinRoot.of _ a) =
      AdjoinRoot.of _ a := by
  simp [cyclotomicSplitMap]

end DivisionFree.Fourier
