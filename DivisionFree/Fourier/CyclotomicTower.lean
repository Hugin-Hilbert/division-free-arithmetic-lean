import DivisionFree.Fourier.BlockReduction
import DivisionFree.Fourier.CyclicRepresentation

/-! The maps between the cyclotomic extensions used in recursive multiplication.
They are defined over every commutative base ring by polynomial identities. -/

namespace DivisionFree.Fourier

open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem cyclotomicTower_relation (p q r : ℕ) (hp : p.Prime) :
    (Polynomial.cyclotomic (p ^ (q + 1)) R).eval₂
      (AdjoinRoot.of (Polynomial.cyclotomic (p ^ (q + r + 1)) R))
      (cyclotomicRoot R (p ^ (q + r + 1)) ^ (p ^ r)) = 0 := by
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := R) (n := q) hp]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have h := cyclotomicRoot_geom_sum (R := R) p (q + r) hp
  rw [Fin.sum_univ_eq_sum_range
    (fun i => cyclotomicRoot R (p ^ (q + r + 1)) ^ (p ^ (q + r) * i)) p] at h
  calc
    ∑ i ∈ Finset.range p,
        ((cyclotomicRoot R (p ^ (q + r + 1)) ^ (p ^ r)) ^ (p ^ q)) ^ i =
        ∑ i ∈ Finset.range p, cyclotomicRoot R (p ^ (q + r + 1)) ^ (p ^ (q + r) * i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [← pow_mul, pow_add]
      congr 1
      ring
    _ = 0 := h

/-- Send the small root to the appropriate power of the large root. -/
noncomputable def cyclotomicTowerMap (p q r : ℕ) (hp : p.Prime) :
    CyclotomicRing R (p ^ (q + 1)) →+* CyclotomicRing R (p ^ (q + r + 1)) :=
  AdjoinRoot.lift (AdjoinRoot.of _) (cyclotomicRoot R (p ^ (q + r + 1)) ^ (p ^ r))
    (cyclotomicTower_relation p q r hp)

@[simp] theorem cyclotomicTowerMap_root (p q r : ℕ) (hp : p.Prime) :
    cyclotomicTowerMap (R := R) p q r hp (cyclotomicRoot R (p ^ (q + 1))) =
      cyclotomicRoot R (p ^ (q + r + 1)) ^ (p ^ r) := by
  simp [cyclotomicTowerMap, cyclotomicRoot]

@[simp] theorem cyclotomicTowerMap_of (p q r : ℕ) (hp : p.Prime) (a : R) :
    cyclotomicTowerMap (R := R) p q r hp (AdjoinRoot.of _ a) = AdjoinRoot.of _ a := by
  simp [cyclotomicTowerMap]

/-- Coefficient evaluation is compatible with the tower map; no field or
characteristic assumption enters this transport. -/
theorem cyclotomicTowerMap_coefficients (p q r : ℕ) (hp : p.Prime)
    [NeZero (p ^ (q + 1))] (x : ZMod (p ^ (q + 1)) → R) :
    cyclotomicTowerMap (R := R) p q r hp (toCyclotomic x) =
      ∑ i : ZMod (p ^ (q + 1)), AdjoinRoot.of _ (x i) *
        (cyclotomicRoot R (p ^ (q + r + 1)) ^ (p ^ r)) ^ i.val := by
  simp only [toCyclotomic, cyclicEval, cyclotomicCharacter, AddChar.zmodChar_apply,
    map_sum, map_mul, map_pow, cyclotomicTowerMap_root, cyclotomicTowerMap_of]

end DivisionFree.Fourier
