import DivisionFree.Fourier.Scatter
import DivisionFree.Fourier.CyclicRepresentation
import DivisionFree.Fourier.FiniteTransform

/-!
# Recombining recursively transformed coefficient arrays
-/

namespace DivisionFree.Fourier

open scoped BigOperators

/-- Scatter small cyclic coefficient blocks into one larger coefficient array. -/
noncomputable def coefficientRecombine (m n L : ℕ) [NeZero m] [NeZero n] :
    Circuit (Fin L × ZMod m) (ZMod (m * n)) :=
  scatter fun ij => ((n * ij.2.val + ij.1.val : ℕ) : ZMod (m * n))

theorem coefficientRecombine_cost (m n L : ℕ) [NeZero m] [NeZero n] :
    (coefficientRecombine m n L).cost = L * m := by
  classical
  simp [coefficientRecombine, scatter_cost]

theorem coefficientRecombine_multiplications (m n L : ℕ) [NeZero m] [NeZero n] :
    (coefficientRecombine m n L).multiplications = 0 := by
  simp [coefficientRecombine, scatter_multiplications]

theorem coefficientRecombine_constantBits (m n L : ℕ) [NeZero m] [NeZero n] :
    (coefficientRecombine m n L).constantBits = 0 := by
  simp [coefficientRecombine, scatter_constantBits]

theorem coefficientRecombine_eval {R : Type*} [Ring R]
    (m n L : ℕ) [NeZero m] [NeZero n]
    (x : Fin L × ZMod m → R) (j : ZMod (m * n)) :
    (coefficientRecombine m n L).eval x j =
      ∑ ij : Fin L × ZMod m,
        if ((n * ij.2.val + ij.1.val : ℕ) : ZMod (m * n)) = j then x ij else 0 := by
  simp [coefficientRecombine, scatter_eval]

theorem coefficientRecombine_transform {R S : Type*} [CommRing R] [CommRing S]
    (m n L : ℕ) [NeZero m] [NeZero n]
    (f : R →+* S) (w : S) (hw : w ^ (m * n) = 1)
    (x : Fin L × ZMod m → R) :
    ∑ j : ZMod (m * n),
        f ((coefficientRecombine m n L).eval x j) * w ^ j.val =
      ∑ k : Fin L,
        (∑ j : ZMod m, f (x (k, j)) * (w ^ n) ^ j.val) * w ^ k.val := by
  classical
  let g : Fin L × ZMod m → ZMod (m * n) :=
    fun ij => ((n * ij.2.val + ij.1.val : ℕ) : ZMod (m * n))
  have hmap (j : ZMod (m * n)) :
      f ((scatter g).eval x j) = (scatter g).eval (fun ij => f (x ij)) j := by
    rw [scatter_eval, scatter_eval, map_sum]
    apply Finset.sum_congr rfl
    intro ij hij
    by_cases h : g ij = j <;> simp [h]
  calc
    ∑ j : ZMod (m * n), f ((scatter g).eval x j) * w ^ j.val =
        ∑ ij : Fin L × ZMod m, f (x ij) * w ^ (g ij).val := by
          simp_rw [hmap]
          exact scatter_weighted_sum g (fun ij => f (x ij)) (fun j => w ^ j.val)
    _ = ∑ k : Fin L,
          (∑ j : ZMod m, f (x (k, j)) * (w ^ n) ^ j.val) * w ^ k.val := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k hk
        calc
          (∑ j : ZMod m, f (x (k, j)) * w ^ (g (k, j)).val) =
              ∑ j : ZMod m, f (x (k, j)) * ((w ^ n) ^ j.val * w ^ k.val) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hpow : w ^ (g (k, j)).val = (w ^ n) ^ j.val * w ^ k.val := by
              dsimp [g]
              rw [ZMod.val_natCast, ← pow_eq_pow_mod (n * j.val + k.val) hw]
              simp [pow_mul, pow_add]
            rw [hpow]
          _ = (∑ j : ZMod m, f (x (k, j)) * (w ^ n) ^ j.val) * w ^ k.val := by
            calc
              (∑ j : ZMod m, f (x (k, j)) * ((w ^ n) ^ j.val * w ^ k.val)) =
                  ∑ j : ZMod m, (f (x (k, j)) * (w ^ n) ^ j.val) * w ^ k.val := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = (∑ j : ZMod m, f (x (k, j)) * (w ^ n) ^ j.val) * w ^ k.val := by
                    exact (Finset.sum_mul Finset.univ _ _).symm

end DivisionFree.Fourier
