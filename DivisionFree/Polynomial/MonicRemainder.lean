import DivisionFree.Polynomial.MonicQuotient
import DivisionFree.Polynomial.MonicEncodingCircuit
import DivisionFree.Circuit.Evaluation

/-! A prepared monic remainder circuit. The stored data consist of the lower
modulus coefficients and the inverse of its reflected prefix. -/

namespace DivisionFree.PolynomialArithmetic

universe u

/-- Inputs are `(lower modulus coefficients, reflected inverse, dividend)`.
The quotient is shared between the multiplication and subtraction stages. -/
noncomputable def preparedRemainder (n : ℕ) :
    Circuit ((Fin n ⊕ Fin n) ⊕ Fin (2 * n)) (Fin n) :=
  .comp
    (.pair (.wire id)
      (.comp (.wire fun j : Fin n ⊕ Fin (2 * n) => match j with
        | .inl i => .inl (.inr i)
        | .inr i => .inr i) (quotientFromInverse.{u} n)))
    (.comp
      (.pair
        (.wire fun i : Fin n => Sum.inl (Sum.inr (Fin.castLE (by omega) i)))
        (.comp (.wire fun j : Bool × Fin n =>
          if j.1 then Sum.inr j.2 else Sum.inl (Sum.inl (Sum.inl j.2)))
          (fastMultiplier.{u} n).circuit))
      (.comp (.wire fun j : Bool × Fin n => if j.1 then Sum.inr j.2 else Sum.inl j.2)
        (vectorSub n)))

theorem preparedRemainder_cost (n : ℕ) :
    (preparedRemainder.{u} n).cost = 2 * (fastMultiplier.{u} n).cost + 2 * n := by
  simp [preparedRemainder, quotientFromInverse_cost, vectorSub_cost, Multiplier.cost]
  omega

theorem preparedRemainder_constantBits (n : ℕ) :
    (preparedRemainder.{u} n).constantBits = 2 * (fastMultiplier.{u} n).circuit.constantBits := by
  simp [preparedRemainder, Circuit.constantBits, quotientFromInverse_constantBits,
    vectorSub_constantBits]
  omega

theorem preparedRemainder_eval {R : Type u} [CommRing R]
    (n : ℕ) (a v : Fin n → R) (h : Fin (2 * n) → R) (i : Fin n) :
    (preparedRemainder.{u} n).eval (Sum.elim (Sum.elim a v) h) i =
      h (Fin.castLE (by omega) i) - (fastMultiplier.{u} n).circuit.eval
        (fun j : Bool × Fin n => if j.1 then
          (quotientFromInverse.{u} n).eval (Sum.elim v h) j.2 else a j.2) i := by
  have hselect : (fun j : Fin n ⊕ Fin (2 * n) =>
      Sum.elim (Sum.elim a v) h (match j with
        | .inl k => .inl (.inr k)
        | .inr k => .inr k)) = Sum.elim v h := by
    funext j
    cases j <;> rfl
  simp only [preparedRemainder, Circuit.eval_comp_function, Circuit.eval_pair_function,
    Circuit.eval_wire_function, vectorSub_eval, Sum.elim_inl, Sum.elim_inr,
    Bool.false_eq_true, if_false, if_true, hselect]
  congr 1
  apply congrArg (fun x : Bool × Fin n → R => (fastMultiplier.{u} n).circuit.eval x i)
  funext j
  rcases j with ⟨b, j⟩
  cases b <;> rfl

theorem preparedRemainder_polynomial {R : Type u} [CommRing R]
    (n : ℕ) (a v : Fin n → R) (h : Fin (2 * n) → R) :
    vectorPolynomial n ((preparedRemainder.{u} n).eval (Sum.elim (Sum.elim a v) h)) =
      vectorPolynomial (2 * n) h %ₘ (Polynomial.X ^ n) -
        (vectorPolynomial n a *
          vectorPolynomial n ((quotientFromInverse.{u} n).eval (Sum.elim v h))) %ₘ
            (Polynomial.X ^ n) := by
  let q := (quotientFromInverse.{u} n).eval (Sum.elim v h)
  let x : Bool × Fin n → R := fun j => if j.1 then q j.2 else a j.2
  have heval : (preparedRemainder.{u} n).eval (Sum.elim (Sum.elim a v) h) =
      (vectorSub n).eval (fun j : Bool × Fin n => if j.1 then
        (fastMultiplier.{u} n).circuit.eval x j.2 else (resize (2 * n) n).eval h j.2) := by
    funext i
    rw [preparedRemainder_eval, vectorSub_eval]
    simp only [Bool.false_eq_true, if_false, if_true, resize_eval,
      show i.val < 2 * n by omega, dif_pos]
    rfl
  rw [heval, vectorPolynomial_vectorSub]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [vectorPolynomial_resize_mod, (fastMultiplier.{u} n).polynomial_correct]
  simp only [x, q, Bool.false_eq_true, if_false, if_true]

/-- The prepared circuit returns the full monic remainder. The modulus is
encoded by its lower coefficients, so degree zero and the zero ring are
included without a degree or nontriviality assumption on the interface. -/
theorem preparedRemainder_correct {R : Type u} [CommRing R]
    (n : ℕ) (a v : Fin n → R) (h : Fin (2 * n) → R)
    (hv : (Polynomial.X : Polynomial R) ^ n ∣
      1 - Polynomial.reflect n (monicPolynomial n a) * vectorPolynomial n v) :
    vectorPolynomial n ((preparedRemainder.{u} n).eval (Sum.elim (Sum.elim a v) h)) =
      vectorPolynomial (2 * n) h %ₘ monicPolynomial n a := by
  classical
  nontriviality R
  by_cases hn : n = 0
  · subst n
    simp [monicPolynomial, vectorPolynomial]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let H := vectorPolynomial (2 * n) h
    let F := monicPolynomial n a
    have hF : F.Monic := monicPolynomial_monic n a
    have hdegF : F.degree = (n : WithBot ℕ) := monicPolynomial_degree n a
    have hrem : (H %ₘ F) %ₘ (Polynomial.X ^ n) = H %ₘ F := by
      apply (Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow n)).2
      rw [Polynomial.degree_X_pow, ← hdegF]
      exact Polynomial.degree_modByMonic_lt H hF
    rw [preparedRemainder_polynomial,
      quotientFromInverse_correct n hnpos F v h hF hdegF hv]
    change H %ₘ (Polynomial.X ^ n) -
      (vectorPolynomial n a * (H /ₘ F)) %ₘ (Polynomial.X ^ n) = H %ₘ F
    rw [← Polynomial.sub_modByMonic]
    have hsplit : H - vectorPolynomial n a * (H /ₘ F) =
        H %ₘ F + Polynomial.X ^ n * (H /ₘ F) := by
      have hdiv := Polynomial.modByMonic_add_div H F
      change H %ₘ F + (Polynomial.X ^ n + vectorPolynomial n a) * (H /ₘ F) = H at hdiv
      linear_combination -hdiv
    rw [hsplit, Polynomial.add_modByMonic, Polynomial.self_mul_modByMonic,
      add_zero, hrem]
    exact Polynomial.monic_X_pow n

end DivisionFree.PolynomialArithmetic
