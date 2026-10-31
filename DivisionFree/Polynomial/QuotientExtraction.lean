import DivisionFree.Polynomial.Encoding
import Mathlib.RingTheory.AdjoinRoot

/-! Uniqueness and extraction for representatives of bounded degree in a
monic polynomial quotient. -/

namespace DivisionFree.PolynomialArithmetic

/-- Two representatives of degree strictly below a monic modulus are equal
when they define the same adjoined-root class. This works over every
commutative ring, including the zero ring. -/
theorem eq_of_mk_eq_of_degree_lt {R : Type*} [CommRing R]
    (f : Polynomial R) (hf : f.Monic) {p q : Polynomial R}
    (hp : p.degree < f.degree) (hq : q.degree < f.degree)
    (h : AdjoinRoot.mk f p = AdjoinRoot.mk f q) : p = q := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    have hpmod : p %ₘ f = p :=
      (Polynomial.modByMonic_eq_self_iff hf).2 hp
    have hqmod : q %ₘ f = q :=
      (Polynomial.modByMonic_eq_self_iff hf).2 hq
    have hdecode := congrArg (AdjoinRoot.modByMonicHom hf) h
    rw [AdjoinRoot.modByMonicHom_mk, hpmod,
      AdjoinRoot.modByMonicHom_mk, hqmod] at hdecode
    exact hdecode
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact Subsingleton.elim _ _

/-- Bounded coefficient-vector encoding is injective in the quotient by a
monic polynomial whose degree equals the vector length. -/
theorem vectorPolynomial_quotient_injective {R : Type*} [CommRing R]
    (f : Polynomial R) (hf : f.Monic) (D : ℕ)
    (hdegree : f.degree = (D : WithBot ℕ)) :
    Function.Injective (fun x : Fin D → R =>
      AdjoinRoot.mk f (vectorPolynomial D x)) := by
  classical
  intro x y hxy
  apply vectorPolynomial_injective
  apply eq_of_mk_eq_of_degree_lt f hf
  · rw [hdegree]
    exact_mod_cast Polynomial.ofFn_degree_lt x
  · rw [hdegree]
    exact_mod_cast Polynomial.ofFn_degree_lt y
  · exact hxy

/-- Equality of quotient classes implies equality of the represented
coefficient vectors. -/
theorem vector_eq_of_mk_eq {R : Type*} [CommRing R]
    (f : Polynomial R) (hf : f.Monic) (D : ℕ)
    (hdegree : f.degree = (D : WithBot ℕ))
    (x y : Fin D → R)
    (hxy : AdjoinRoot.mk f (vectorPolynomial D x) =
      AdjoinRoot.mk f (vectorPolynomial D y)) : x = y :=
  vectorPolynomial_quotient_injective f hf D hdegree hxy

end DivisionFree.PolynomialArithmetic
