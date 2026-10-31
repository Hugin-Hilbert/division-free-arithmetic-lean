import DivisionFree.Polynomial.VectorEvaluation

/-! Two-block evaluation for polynomials of degree less than `2*n`. -/

namespace DivisionFree.Fourier

open DivisionFree.PolynomialArithmetic
open scoped BigOperators

theorem eval_twoBlock_coefficients {S : Type*} [CommRing S]
    (n : ℕ) (c : Polynomial S)
    (hc : ∀ k, 2 * n ≤ k → c.coeff k = 0)
    (w z : S) (hw : w ^ n = z) :
    c.eval w = ∑ k : Fin n,
      (c.coeff k.val + z * c.coeff (n + k.val)) * w ^ k.val := by
  classical
  have hrepr := vectorPolynomial_coefficients (2 * n) c hc
  have heval := congrArg (fun p : Polynomial S => p.eval₂ (RingHom.id S) w) hrepr
  have hsum : c.eval w = ∑ i : Fin (2 * n), c.coeff i.val * w ^ i.val := by
    simpa only [Polynomial.eval₂_id, vectorPolynomial_eval₂, RingHom.id_apply] using heval.symm
  have hsplit := hsum
  rw [show 2 * n = n + n by omega, Fin.sum_univ_add] at hsplit
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hsplit
  have hupper :
      (∑ i : Fin n, c.coeff (n + i.val) * w ^ (n + i.val)) =
        ∑ i : Fin n, (z * c.coeff (n + i.val)) * w ^ i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add, hw]
    ring
  rw [hupper] at hsplit
  calc
    c.eval w =
        (∑ i : Fin n, c.coeff i.val * w ^ i.val) +
          ∑ i : Fin n, (z * c.coeff (n + i.val)) * w ^ i.val := hsplit
    _ = ∑ i : Fin n,
          (c.coeff i.val + z * c.coeff (n + i.val)) * w ^ i.val := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end DivisionFree.Fourier
