import DivisionFree.Fourier.CyclicRadix
import DivisionFree.Fourier.FiniteTransform

/-!
# A coefficient-level Fourier multiplication step

The pointwise multiplier is an actual circuit, whose cost is charged at every
call. The surrounding transforms are already base-ring circuits. This module
is the induction step, not an existence assumption for a fast multiplier.
-/

namespace DivisionFree.Fourier

open scoped BigOperators
noncomputable section

variable (M : ℕ) [NeZero M]

def forwardPair (s : ℕ) (hs : 0 < s) (r : ℕ) (e : ZMod M) :
    Circuit (Bool × (Fin (s ^ r) × ZMod M)) (Bool × (Fin (s ^ r) × ZMod M)) :=
  .bundle fun b : Bool =>
    .comp (.wire fun j => (b, j)) (cyclicRadix M s hs r e)

private theorem forwardPair_cost (s : ℕ) (hs : 0 < s) (r : ℕ) (e : ZMod M) :
    (forwardPair M s hs r e).cost = 2 * (M * s * r * s ^ r) := by
  simp [forwardPair, cyclicRadix_cost, two_mul]

def pointwise (n : ℕ) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    Circuit (Bool × (Fin n × ZMod M)) (Fin n × ZMod M) :=
  .bundle fun k : Fin n => .comp (.wire fun j : Bool × ZMod M => (j.1, (k, j.2))) P

private theorem pointwise_cost (n : ℕ) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (pointwise M n P).cost = n * P.cost := by simp [pointwise]

/-- Forward transforms, charged pointwise calls, and an inverse-sign transform
implemented by reversing the outputs of the same forward transform. -/
def cyclicProduct (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (e : ZMod M) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    Circuit (Bool × (Fin (s ^ r) × ZMod M)) (Fin (s ^ r) × ZMod M) :=
  .comp (forwardPair M s hs r e)
    (.comp (pointwise M (s ^ r) P)
      (.comp (cyclicRadix M s hs r e)
        (.wire fun j => (negIndex (s ^ r) j.1, j.2))))

theorem cyclicProduct_cost (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (e : ZMod M) (P : Circuit (Bool × ZMod M) (ZMod M)) :
    (cyclicProduct M s hs r e P).cost =
      3 * M * s * r * s ^ r + s ^ r * P.cost := by
  simp only [cyclicProduct, Circuit.comp_cost, Circuit.wire_cost,
    forwardPair_cost, pointwise_cost, cyclicRadix_cost]
  ring

/-- Correctness of one multiplication step, with the semantics of every
pointwise circuit call stated explicitly. -/
theorem cyclicProduct_correct {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S)
    (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (ψ : AddChar (ZMod (s ^ r)) S) (hψ : Orthogonal ψ)
    (e : ZMod M) (he : χ e = ψ 1) (d : S)
    (P : Circuit (Bool × ZMod M) (ZMod M))
    (hP : ∀ z : Bool × ZMod M → R,
      cyclicEval f χ (P.eval z) = d *
        (cyclicEval f χ (fun j => z (false, j)) * cyclicEval f χ (fun j => z (true, j))))
    (x : Bool × (Fin (s ^ r) × ZMod M) → R) (k : Fin (s ^ r)) :
    cyclicEval f χ (fun j => (cyclicProduct M s hs r e P).eval x (k, j)) =
      d * (s ^ r : ℕ) * convolution
        (fun i => cyclicEval f χ (fun j => x (false, ((cyclicIndexEquiv (s ^ r)).symm i, j))))
        (fun i => cyclicEval f χ (fun j => x (true, ((cyclicIndexEquiv (s ^ r)).symm i, j))))
        (cyclicIndexEquiv (s ^ r) k) := by
  have hroot : χ e ^ (s ^ r) = 1 := by
    rw [he, ← ψ.map_nsmul_eq_pow]
    simp [nsmul_eq_mul]
  let A : Fin (s ^ r) → S := fun i => cyclicEval f χ (fun j => x (false, (i, j)))
  let B : Fin (s ^ r) → S := fun i => cyclicEval f χ (fun j => x (true, (i, j)))
  let y := (forwardPair M s hs r e).eval x
  let z := (pointwise M (s ^ r) P).eval y
  have hy (b : Bool) (i : Fin (s ^ r)) :
      cyclicEval f χ (fun j => y (b, (i, j))) =
        finTransform (χ e) (fun t => cyclicEval f χ (fun j => x (b, (t, j)))) i := by
    have hh : (fun j => y (b, (i, j))) =
        (fun j => (cyclicRadix M s hs r e).eval (fun t => x (b, t)) (i, j)) := by
      funext j
      simp only [y, forwardPair, Circuit.eval_bundle, Circuit.eval_comp]
      rfl
    rw [hh]
    exact cyclicRadix_correct M f χ s hs r e hroot _ i
  have hz (i : Fin (s ^ r)) : cyclicEval f χ (fun j => z (i, j)) =
      d * (finTransform (ψ 1) A i * finTransform (ψ 1) B i) := by
    have hh : (fun j => z (i, j)) = P.eval (fun j => y (j.1, (i, j.2))) := by
      funext j
      simp only [z, pointwise, Circuit.eval_bundle, Circuit.eval_comp]
      rfl
    rw [hh]
    rw [hP, hy false, hy true, he]
  have hzfun : (fun i => cyclicEval f χ (fun j => z (i, j))) =
      (fun i => d * (finTransform (ψ 1) A i * finTransform (ψ 1) B i)) := funext hz
  have h := cyclicRadix_correct M f χ s hs r e hroot z (negIndex (s ^ r) k)
  rw [hzfun, he, finTransform_scaled_convolution ψ hψ d A B k] at h
  simpa only [cyclicProduct, Circuit.eval_comp, Circuit.eval_wire, z, y, A, B] using h

end
end DivisionFree.Fourier
