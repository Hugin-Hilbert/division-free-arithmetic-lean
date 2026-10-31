import DivisionFree.Fourier.PowerTable
import DivisionFree.Fourier.Radix
import DivisionFree.Fourier.Cyclotomic

/-! Radix transforms with their root-power preparation charged explicitly. -/

namespace DivisionFree.Fourier

/-- Prepare all powers of the supplied root while retaining the coefficients. -/
def prepareRoots (n : ℕ) (hn : 0 < n) :
    Circuit (PUnit ⊕ Fin n) (Fin n ⊕ Fin n) :=
  .comp
    (.pair (.comp (.wire (fun _ : PUnit => Sum.inl PUnit.unit)) (powerTable (n - 1)))
      (.wire Sum.inr))
    (.wire fun j => match j with
      | .inl i => .inl ⟨i.val, by omega⟩
      | .inr i => .inr i)

theorem prepareRoots_cost (n : ℕ) (hn : 0 < n) :
    (prepareRoots n hn).cost = n - 1 := by
  simp [prepareRoots, powerTable_cost]

theorem prepareRoots_eval {R : Type*} [Ring R] (n : ℕ) (hn : 0 < n)
    (w : R) (a : Fin n → R) :
    (prepareRoots n hn).eval (Sum.elim (fun _ => w) a) =
      Sum.elim (fun i => w ^ i.val) a := by
  funext j
  cases j <;> simp [prepareRoots, powerTable_eval]

/-- The root is an input; all its powers are computed within this circuit. -/
noncomputable def preparedRadixTransform (s : ℕ) (hs : 0 < s) (r : ℕ) :
    Circuit (PUnit ⊕ Fin (s ^ r)) (Fin (s ^ r)) :=
  .comp (prepareRoots (s ^ r) (pow_pos hs r)) (radixTransform s hs r)

theorem preparedRadixTransform_cost (s : ℕ) (hs : 0 < s) (r : ℕ) :
    (preparedRadixTransform s hs r).cost = s ^ r - 1 + 2 * s * r * s ^ r := by
  simp [preparedRadixTransform, prepareRoots_cost, radixTransform_cost]

theorem preparedRadixTransform_eval {R : Type*} [CommRing R]
    (s : ℕ) (hs : 0 < s) (r : ℕ) (w : R) (hw : w ^ (s ^ r) = 1)
    (a : Fin (s ^ r) → R) (k : Fin (s ^ r)) :
    (preparedRadixTransform s hs r).eval (Sum.elim (fun _ => w) a) k =
      (PolynomialArithmetic.vectorPolynomial (s ^ r) a).eval (w ^ k.val) := by
  rw [preparedRadixTransform, Circuit.eval_comp, prepareRoots_eval,
    radixTransform_eval_polynomial s hs r w hw]

/-- Instantiation in a cyclotomic extension over an arbitrary base ring.
No roots of unity or invertible integers are required in the base ring. -/
theorem preparedRadixTransform_cyclotomic {R : Type*} [CommRing R]
    (N : ℕ) [NeZero N] (s : ℕ) (hs : 0 < s) (r : ℕ) (hdiv : s ^ r ∣ N)
    (a : Fin (s ^ r) → CyclotomicRing R N) (k : Fin (s ^ r)) :
    (preparedRadixTransform s hs r).eval
      (Sum.elim (fun _ => cyclotomicRoot R N ^ (N / s ^ r)) a) k =
      (PolynomialArithmetic.vectorPolynomial (s ^ r) a).eval
        ((cyclotomicRoot R N ^ (N / s ^ r)) ^ k.val) :=
  preparedRadixTransform_eval s hs r _ (cyclotomicSubroot_pow R N _ hdiv) a k

end DivisionFree.Fourier
