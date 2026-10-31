import DivisionFree.Fourier.CyclicInput
import DivisionFree.Fourier.CyclotomicMultiplier
import DivisionFree.Polynomial.QuotientExtraction

/-! Extract the entire ordinary polynomial product from a normalized cyclic
representation, with a degree bound covering every product coefficient. -/

namespace DivisionFree.Fourier

open PolynomialArithmetic

noncomputable def cyclicFullProduct (n m : ℕ) [NeZero m]
    (P : Circuit (Bool × ZMod m) (ZMod m)) (N : Circuit (ZMod m) (ZMod m)) :
    Circuit (Bool × Fin n) (Fin (2 * n)) :=
  .comp (cyclicInput n m)
    (.comp P (.comp N (.wire fun k : Fin (2 * n) => (k.val : ZMod m))))

theorem cyclicFullProduct_cost (n m : ℕ) [NeZero m]
    (P : Circuit (Bool × ZMod m) (ZMod m)) (N : Circuit (ZMod m) (ZMod m)) :
    (cyclicFullProduct n m P N).cost = P.cost + N.cost := by
  simp [cyclicFullProduct, cyclicInput_cost]

theorem cyclicFullProduct_correct {R : Type*} [CommRing R]
    (n m D : ℕ) [NeZero m] (hlen : 2 * n ≤ D) (hD : D ≤ m)
    (hdegree : (Polynomial.cyclotomic m R).degree = (D : WithBot ℕ))
    (d : ℕ) (P : Circuit (Bool × ZMod m) (ZMod m)) (N : Circuit (ZMod m) (ZMod m))
    (hP : ∀ y : Bool × ZMod m → R, toCyclotomic (P.eval y) = (d : CyclotomicRing R m) *
      (toCyclotomic (fun j => y (false, j)) * toCyclotomic (fun j => y (true, j))))
    (hN : ∀ y : ZMod m → R, toCyclotomic (N.eval y) = toCyclotomic y)
    (htail : ∀ (y : ZMod m → R) (j : ZMod m), D ≤ j.val → N.eval y j = 0)
    (x : Bool × Fin n → R) :
    vectorPolynomial (2 * n) ((cyclicFullProduct n m P N).eval x) =
      Polynomial.C (d : R) * (vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i))) := by
  let y := (cyclicInput n m).eval x
  let z := N.eval (P.eval y)
  let q := Polynomial.C (d : R) * (vectorPolynomial n (fun i => x (false, i)) *
    vectorPolynomial n (fun i => x (true, i)))
  have hq (k : ℕ) (hk : 2 * n ≤ k) : q.coeff k = 0 := by
    dsimp [q]
    rw [Polynomial.coeff_C_mul,
      vectorPolynomial_mul_coeff_eq_zero_of_ge n k _ _ (by omega), mul_zero]
  have hz (k : ℕ) (hk : D ≤ k) : (toPolynomial z).coeff k = 0 := by
    by_cases hkm : k < m
    · have hval : (k : ZMod m).val = k := ZMod.val_natCast_of_lt hkm
      have hc := toPolynomial_coeff z (k : ZMod m)
      rw [hval] at hc
      rw [hc]
      exact htail (P.eval y) (k : ZMod m) (by simpa only [hval] using hk)
    · exact toPolynomial_coeff_zero z k (by omega)
  have hclass : AdjoinRoot.mk (Polynomial.cyclotomic m R) (toPolynomial z) =
      AdjoinRoot.mk (Polynomial.cyclotomic m R) q := by
    rw [← toCyclotomic_eq_mk]
    change toCyclotomic (N.eval (P.eval y)) = _
    rw [hN, hP, toCyclotomic_eq_mk, toCyclotomic_eq_mk]
    dsimp [y, q]
    rw [cyclicInput_toPolynomial n m (by omega) x false,
      cyclicInput_toPolynomial n m (by omega) x true]
    simp only [map_mul, map_natCast]
  have hpoly : toPolynomial z = q := by
    apply eq_of_mk_eq_of_degree_lt (Polynomial.cyclotomic m R) (Polynomial.cyclotomic.monic m R)
    · rw [hdegree]
      exact (Polynomial.degree_lt_iff_coeff_zero _ D).mpr hz
    · rw [hdegree]
      exact (Polynomial.degree_lt_iff_coeff_zero _ D).mpr (fun k hk => hq k (by omega))
    · exact hclass
  apply Polynomial.ext
  intro k
  by_cases hk : k < 2 * n
  · rw [vectorPolynomial_coeff_of_lt (2 * n) k _ hk]
    simp only [cyclicFullProduct, Circuit.eval_comp, Circuit.eval_wire]
    change z (k : ZMod m) = q.coeff k
    have hc := congrArg (fun a : Polynomial R => a.coeff (k : ZMod m).val) hpoly
    rw [toPolynomial_coeff, ZMod.val_natCast_of_lt (show k < m by omega)] at hc
    exact hc
  · rw [vectorPolynomial_coeff_eq_zero_of_ge (2 * n) k _ (by omega)]
    exact (hq k (by omega)).symm

end DivisionFree.Fourier
