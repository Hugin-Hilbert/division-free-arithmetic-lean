import DivisionFree.Polynomial.NewtonStep
import DivisionFree.Polynomial.VectorReverse
import DivisionFree.Polynomial.MonicDivisionBounds
import DivisionFree.Polynomial.QuotientExtraction

/-! Recover a monic quotient using one truncated product with the prepared
inverse of the reflected modulus. Both reversals are wires. -/

namespace DivisionFree.PolynomialArithmetic

universe u

/-- Inputs are the prepared inverse and the length-`2*n` dividend. -/
noncomputable def quotientFromInverse (n : ℕ) :
    Circuit (Fin n ⊕ Fin (2 * n)) (Fin n) :=
  .comp (.pair (.comp (.wire Sum.inr) (highReverse n)) (.wire Sum.inl))
    (.comp (.wire fun j : Bool × Fin n => if j.1 then Sum.inr j.2 else Sum.inl j.2)
      (.comp (fastMultiplier.{u} n).circuit (reverseVector n)))

theorem quotientFromInverse_cost (n : ℕ) :
    (quotientFromInverse.{u} n).cost = (fastMultiplier.{u} n).cost := by
  simp [quotientFromInverse, highReverse_cost, reverseVector_cost, Multiplier.cost]

theorem quotientFromInverse_constantBits (n : ℕ) :
    (quotientFromInverse.{u} n).constantBits = (fastMultiplier.{u} n).circuit.constantBits := by
  simp [quotientFromInverse, Circuit.constantBits, highReverse_constantBits,
    reverseVector_constantBits]

theorem quotientFromInverse_polynomial {R : Type u} [CommRing R]
    (n : ℕ) (v : Fin n → R) (h : Fin (2 * n) → R) :
    vectorPolynomial n ((quotientFromInverse.{u} n).eval (Sum.elim v h)) =
      Polynomial.reflect (n - 1)
        (((Polynomial.reflect (2 * n - 1) (vectorPolynomial (2 * n) h) %ₘ
          (Polynomial.X ^ n)) * vectorPolynomial n v) %ₘ (Polynomial.X ^ n)) := by
  let x : Bool × Fin n → R := fun j =>
    if j.1 then v j.2 else (highReverse n).eval h j.2
  have heval : (quotientFromInverse.{u} n).eval (Sum.elim v h) =
      (reverseVector n).eval ((fastMultiplier.{u} n).circuit.eval x) := by
    funext i
    simp only [quotientFromInverse, Circuit.eval_comp, reverseVector_eval]
    apply congrArg (fun z : Bool × Fin n → R =>
      (fastMultiplier.{u} n).circuit.eval z (Fin.rev i))
    funext j
    rcases j with ⟨b, j⟩
    cases b <;> simp [x]
  rw [heval, vectorPolynomial_reverse, (fastMultiplier.{u} n).polynomial_correct]
  simp only [x, Bool.false_eq_true, if_false, if_true]
  rw [vectorPolynomial_highReverse_mod]

/-- Algebraic reverse-division identity. The inverse is taken only modulo
`X^n`, and the dividend bound covers its complete high half. -/
theorem monicQuotient_reflection {R : Type*} [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : 0 < n) (F h v : Polynomial R)
    (hF : F.Monic) (hdegF : F.degree = (n : WithBot ℕ))
    (hdegh : h.degree < ((2 * n : ℕ) : WithBot ℕ))
    (hv : (Polynomial.X : Polynomial R) ^ n ∣ 1 - Polynomial.reflect n F * v) :
    Polynomial.reflect (n - 1)
      (((Polynomial.reflect (2 * n - 1) h %ₘ (Polynomial.X ^ n)) * v) %ₘ
        (Polynomial.X ^ n)) = h /ₘ F := by
  let φ := AdjoinRoot.mk ((Polynomial.X : Polynomial R) ^ n)
  have hunit : φ (Polynomial.reflect n F) * φ v = 1 := by
    have hh := AdjoinRoot.mk_eq_zero.mpr hv
    simp only [map_sub, map_one, map_mul] at hh
    exact (sub_eq_zero.mp hh).symm
  have hcong : φ (Polynomial.reflect (2 * n - 1) h) =
      φ (Polynomial.reflect n F) * φ (Polynomial.reflect (n - 1) (h /ₘ F)) := by
    have hh := AdjoinRoot.mk_eq_mk.mpr
      (reflect_monicDivision_congruence hn F h hF hdegF hdegh)
    simpa only [map_mul] using hh
  let W := ((Polynomial.reflect (2 * n - 1) h %ₘ (Polynomial.X ^ n)) * v) %ₘ
    (Polynomial.X ^ n)
  have hclass : φ W = φ (Polynomial.reflect (n - 1) (h /ₘ F)) := by
    simp only [W, φ, mk_modByMonic, map_mul]
    change φ (Polynomial.reflect (2 * n - 1) h) * φ v = _
    rw [hcong]
    calc
      (φ (Polynomial.reflect n F) * φ (Polynomial.reflect (n - 1) (h /ₘ F))) * φ v =
          (φ (Polynomial.reflect n F) * φ v) * φ (Polynomial.reflect (n - 1) (h /ₘ F)) := by ring
      _ = _ := by rw [hunit, one_mul]
  have hqnd := (monicDivision_degree_bounds hn F h hF hdegF hdegh).1
  have hrefnd : (Polynomial.reflect (n - 1) (h /ₘ F)).natDegree ≤ n - 1 :=
    Polynomial.natDegree_reflect_le.trans (max_le_iff.mpr ⟨le_rfl, hqnd⟩)
  have hW : W = Polynomial.reflect (n - 1) (h /ₘ F) := by
    apply eq_of_mk_eq_of_degree_lt (Polynomial.X ^ n) (Polynomial.monic_X_pow n)
    · exact Polynomial.degree_modByMonic_lt _ (Polynomial.monic_X_pow n)
    · rw [Polynomial.degree_X_pow]
      exact Polynomial.degree_le_natDegree.trans_lt
        (by exact_mod_cast (show (Polynomial.reflect (n - 1) (h /ₘ F)).natDegree < n by omega))
    · exact hclass
  change Polynomial.reflect (n - 1) W = h /ₘ F
  rw [hW, Polynomial.reflect_reflect]

theorem quotientFromInverse_correct {R : Type u} [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : 0 < n) (F : Polynomial R) (v : Fin n → R) (h : Fin (2 * n) → R)
    (hF : F.Monic) (hdegF : F.degree = (n : WithBot ℕ))
    (hv : (Polynomial.X : Polynomial R) ^ n ∣
      1 - Polynomial.reflect n F * vectorPolynomial n v) :
    vectorPolynomial n ((quotientFromInverse.{u} n).eval (Sum.elim v h)) =
      vectorPolynomial (2 * n) h /ₘ F := by
  classical
  rw [quotientFromInverse_polynomial]
  apply monicQuotient_reflection n hn F _ _ hF hdegF
  · simpa [vectorPolynomial] using Polynomial.ofFn_degree_lt h
  · exact hv

end DivisionFree.PolynomialArithmetic
