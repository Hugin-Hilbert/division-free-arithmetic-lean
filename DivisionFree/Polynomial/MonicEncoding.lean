import DivisionFree.Polynomial.Encoding
import Mathlib.RingTheory.AdjoinRoot

/-! Bounded coefficient vectors for quotients by monic polynomials. -/

namespace DivisionFree.PolynomialArithmetic

/-- Encode a bounded coefficient vector as a residue class modulo a monic
polynomial. -/
noncomputable def monicEncode {R : Type*} [CommRing R] (f : Polynomial R)
    (_hf : f.Monic) (x : Fin f.natDegree → R) : AdjoinRoot f :=
  AdjoinRoot.mk f (vectorPolynomial f.natDegree x)

theorem monicEncode_injective {R : Type*} [CommRing R] (f : Polynomial R)
    (hf : f.Monic) :
    Function.Injective (monicEncode f hf) := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    intro x y hxy
    apply funext
    intro i
    have hdec := congrArg (AdjoinRoot.modByMonicHom hf) hxy
    simp only [monicEncode, AdjoinRoot.modByMonicHom_mk] at hdec
    have hdeg (z : Fin f.natDegree → R) :
        (vectorPolynomial f.natDegree z).degree < f.degree := by
      rw [Polynomial.degree_eq_natDegree hf.ne_zero]
      exact_mod_cast (Polynomial.ofFn_degree_lt z)
    rw [(Polynomial.modByMonic_eq_self_iff hf).2 (hdeg x),
      (Polynomial.modByMonic_eq_self_iff hf).2 (hdeg y)] at hdec
    have hc := congrArg (fun p : Polynomial R => p.coeff i.val) hdec
    simpa [vectorPolynomial_coeff_of_lt] using hc
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    intro x y hxy
    exact Subsingleton.elim x y

theorem monicEncode_surjective {R : Type*} [CommRing R] (f : Polynomial R)
    (hf : f.Monic) :
    Function.Surjective (monicEncode f hf) := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    intro z
    let p : Polynomial R := AdjoinRoot.modByMonicHom hf z
    let x : Fin f.natDegree → R := fun i => p.coeff i.val
    have hrem : p.degree < f.degree := by
      dsimp [p]
      induction z using AdjoinRoot.induction_on with
      | _ g =>
          simp only [AdjoinRoot.modByMonicHom_mk]
          exact Polynomial.degree_modByMonic_lt g hf
    have hpoly : vectorPolynomial f.natDegree x = p := by
      apply Polynomial.ext
      intro i
      by_cases hi : i < f.natDegree
      · simp [x, vectorPolynomial_coeff_of_lt, hi]
      · have hbound : p.degree < (i : WithBot ℕ) := by
          have hfn : f.degree = (f.natDegree : WithBot ℕ) :=
            Polynomial.degree_eq_natDegree hf.ne_zero
          have hfi : f.degree ≤ (i : WithBot ℕ) := by
            rw [hfn]
            exact WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hi)
          exact hrem.trans_le hfi
        rw [vectorPolynomial_coeff_eq_zero_of_ge f.natDegree i x
          (Nat.le_of_not_gt hi)]
        symm
        exact Polynomial.coeff_eq_zero_of_degree_lt hbound
    refine ⟨x, ?_⟩
    change AdjoinRoot.mk f (vectorPolynomial f.natDegree x) = z
    calc
      AdjoinRoot.mk f (vectorPolynomial f.natDegree x) = AdjoinRoot.mk f p :=
        congrArg (AdjoinRoot.mk f) hpoly
      _ = z := AdjoinRoot.mk_leftInverse hf z
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    intro z
    induction z using AdjoinRoot.induction_on with
    | _ g =>
        refine ⟨fun _ => 0, ?_⟩
        change AdjoinRoot.mk f (vectorPolynomial f.natDegree (fun _ => 0)) =
          AdjoinRoot.mk f g
        exact congrArg (AdjoinRoot.mk f) (Subsingleton.elim _ _)

end DivisionFree.PolynomialArithmetic
