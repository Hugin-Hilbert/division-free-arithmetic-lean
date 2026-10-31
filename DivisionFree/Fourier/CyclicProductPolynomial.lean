import DivisionFree.Fourier.CyclicProduct
import DivisionFree.Fourier.CyclicRepresentation
import DivisionFree.Fourier.CyclicSchoolbook

/-! Coefficient-level polynomial correctness for cyclic product circuits. -/

namespace DivisionFree.Fourier

open scoped BigOperators

/-- A cyclic product circuit computes each coefficient of the ordinary
polynomial product, scaled by the transform length, when the inputs and their
full product have no coefficients beyond that length. The scale is retained;
no cancellation assumption is made. -/
theorem cyclicProduct_polynomial_correct
    {M : ℕ} [NeZero M] {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S)
    (s : ℕ) (hs : 0 < s) (r : ℕ) [NeZero (s ^ r)]
    (ψ : AddChar (ZMod (s ^ r)) S) (hψ : Orthogonal ψ)
    (e : ZMod M) (he : χ e = ψ 1) (d : S)
    (P : Circuit (Bool × ZMod M) (ZMod M))
    (hP : ∀ z : Bool × ZMod M → R,
      cyclicEval f χ (P.eval z) = d *
        (cyclicEval f χ (fun j => z (false, j)) *
          cyclicEval f χ (fun j => z (true, j))))
    (p q : Polynomial S)
    (hp : ∀ k, s ^ r ≤ k → p.coeff k = 0)
    (hq : ∀ k, s ^ r ≤ k → q.coeff k = 0)
    (hpq : ∀ k, s ^ r ≤ k → (p * q).coeff k = 0)
    (x : Bool × (Fin (s ^ r) × ZMod M) → R)
    (hx₀ : ∀ i : Fin (s ^ r),
      cyclicEval f χ (fun j => x (false, (i, j))) = p.coeff i.val)
    (hx₁ : ∀ i : Fin (s ^ r),
      cyclicEval f χ (fun j => x (true, (i, j))) = q.coeff i.val)
    (k : Fin (s ^ r)) :
    cyclicEval f χ (fun j =>
      (cyclicProduct M s hs r e P).eval x (k, j)) =
      d * ((s ^ r : ℕ) : S) * (p * q).coeff k.val := by
  have hstep := cyclicProduct_correct M f χ s hs r ψ hψ e he d P hP x k
  have hA : ∀ i : ZMod (s ^ r),
      cyclicEval f χ (fun j => x (false, ((cyclicIndexEquiv (s ^ r)).symm i, j))) =
        p.coeff i.val := by
    intro i
    simpa [cyclicIndexEquiv] using hx₀ ((cyclicIndexEquiv (s ^ r)).symm i)
  have hB : ∀ i : ZMod (s ^ r),
      cyclicEval f χ (fun j => x (true, ((cyclicIndexEquiv (s ^ r)).symm i, j))) =
        q.coeff i.val := by
    intro i
    simpa [cyclicIndexEquiv] using hx₁ ((cyclicIndexEquiv (s ^ r)).symm i)
  rw [hstep]
  simp_rw [hA, hB]
  have hscaled := scaled_convolution_coefficients ψ hψ p q hp hq hpq
    (cyclicIndexEquiv (s ^ r) k)
  calc
    d * ((s ^ r : ℕ) : S) *
        convolution (fun i : ZMod (s ^ r) => p.coeff i.val)
          (fun i : ZMod (s ^ r) => q.coeff i.val) (cyclicIndexEquiv (s ^ r) k) =
        d * (((s ^ r : ℕ) : S) *
          convolution (fun i : ZMod (s ^ r) => p.coeff i.val)
            (fun i : ZMod (s ^ r) => q.coeff i.val) (cyclicIndexEquiv (s ^ r) k)) := by simp [mul_assoc]
    _ = d * (((s ^ r : ℕ) : S) * (p * q).coeff (cyclicIndexEquiv (s ^ r) k).val) := by
      rw [hscaled]
    _ = d * ((s ^ r : ℕ) : S) * (p * q).coeff k.val := by
      have hkval : (cyclicIndexEquiv (s ^ r) k).val = k.val := by
        simp [cyclicIndexEquiv, ZMod.val_natCast_of_lt k.isLt]
      rw [hkval]
      simp [mul_assoc]

/-- The schoolbook cyclic circuit evaluates to the product of the two
represented values under the cyclic evaluation map. -/
theorem cyclicSchoolbook_correct {M : ℕ} [NeZero M]
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S)
    (x : Bool × ZMod M → R) :
    cyclicEval f χ (fun j => (cyclicSchoolbook M).eval x j) =
      cyclicEval f χ (fun j => x (false, j)) *
        cyclicEval f χ (fun j => x (true, j)) := by
  have heval : (fun j => (cyclicSchoolbook M).eval x j) =
      convolution (fun j => x (false, j)) (fun j => x (true, j)) := by
    funext j
    exact cyclicSchoolbook_eval M x j
  rw [heval]
  exact cyclicEval_convolution f χ _ _

end DivisionFree.Fourier
