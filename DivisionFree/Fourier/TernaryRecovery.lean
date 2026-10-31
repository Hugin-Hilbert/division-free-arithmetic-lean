import DivisionFree.Fourier.CyclicRepresentation
import DivisionFree.Circuit.Evaluation
import DivisionFree.Constants

/-! A division-free recovery transform for ternary coefficient splitting. -/

namespace DivisionFree.Fourier

open DivisionFree

variable (M : ℕ) [NeZero M]

private def ternaryInputStage (e : ZMod M) :
    Circuit (Bool × ZMod M) (Bool × ZMod M) :=
  .comp
    (.bundle fun ij : Bool × ZMod M =>
      Circuit.sum
        (.wire fun _ : PUnit => if ij.1 then (false, ij.2) else (true, ij.2))
        (Circuit.negative (.wire fun _ : PUnit =>
          if ij.1 then (true, ij.2) else (false, ij.2 - e))))
    (.wire fun ij => (ij, PUnit.unit))

private def ternaryOutputStage (e : ZMod M) :
    Circuit (Bool × ZMod M) (Bool × ZMod M) :=
  .comp
    (.bundle fun ij : Bool × ZMod M =>
      Circuit.sum
        (.wire fun _ : PUnit => ij)
        (Circuit.negative (.wire fun _ : PUnit => (ij.1, ij.2 - 2 • e))))
    (.wire fun ij => (ij, PUnit.unit))

/-- Recover the two scaled components from the two evaluations at `1` and
`ζ`, using the factor `1-ζ²` without division. -/
def ternaryRecovery (e : ZMod M) :
    Circuit (Bool × ZMod M) (Bool × ZMod M) :=
  .comp (ternaryInputStage M e) (ternaryOutputStage M e)

private theorem ternaryInputStage_eval {R : Type*} [Ring R]
    (e : ZMod M) (x : Bool × ZMod M → R) (b : Bool) (j : ZMod M) :
    (ternaryInputStage M e).eval x (b, j) =
      if b then x (false, j) - x (true, j)
      else x (true, j) - x (false, j - e) := by
  cases b <;> simp [ternaryInputStage, sub_eq_add_neg]

private theorem ternaryOutputStage_eval {R : Type*} [Ring R]
    (e : ZMod M) (x : Bool × ZMod M → R) (b : Bool) (j : ZMod M) :
    (ternaryOutputStage M e).eval x (b, j) = x (b, j) - x (b, j - 2 • e) := by
  simp [ternaryOutputStage, sub_eq_add_neg]

@[simp] theorem ternaryRecovery_eval {R : Type*} [Ring R]
    (e : ZMod M) (x : Bool × ZMod M → R) (b : Bool) (j : ZMod M) :
    (ternaryRecovery M e).eval x (b, j) =
      (ternaryInputStage M e).eval x (b, j) -
        (ternaryInputStage M e).eval x (b, j - 2 • e) := by
  simp [ternaryRecovery, ternaryOutputStage_eval]

theorem ternaryRecovery_cost (e : ZMod M) :
    (ternaryRecovery M e).cost = 8 * M := by
  classical
  simp [ternaryRecovery, ternaryInputStage, ternaryOutputStage,
    Circuit.sum_cost, Circuit.negative_cost, ZMod.card]
  ring

theorem ternaryRecovery_multiplications (e : ZMod M) :
    (ternaryRecovery M e).multiplications = 0 := by
  classical
  simp [ternaryRecovery, ternaryInputStage, ternaryOutputStage,
    Circuit.multiplications, Circuit.sum]

theorem ternaryRecovery_constantBits (e : ZMod M) :
    (ternaryRecovery M e).constantBits = 0 := by
  classical
  simp [ternaryRecovery, ternaryInputStage, ternaryOutputStage,
    Circuit.constantBits, Circuit.sum, Circuit.negative]

private theorem cyclicEval_sub {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S)
    (x y : ZMod M → R) :
    cyclicEval f χ (fun j => x j - y j) = cyclicEval f χ x - cyclicEval f χ y := by
  simp [sub_eq_add_neg]

theorem ternaryRecovery_cyclicEval_low {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S) (e : ZMod M)
    (x : Bool × ZMod M → R) :
    cyclicEval f χ (fun j => (ternaryRecovery M e).eval x (false, j)) =
      (1 - χ e ^ 2) *
        (cyclicEval f χ (fun j => x (true, j)) -
          χ e * cyclicEval f χ (fun j => x (false, j))) := by
  have hfirst : cyclicEval f χ
      (fun j => (ternaryInputStage M e).eval x (false, j)) =
      cyclicEval f χ (fun j => x (true, j)) -
        χ e * cyclicEval f χ (fun j => x (false, j)) := by
    simp only [ternaryInputStage_eval, Bool.false_eq_true, ↓reduceIte]
    calc
      cyclicEval f χ (fun j => x (true, j) - x (false, j - e)) =
          cyclicEval f χ (fun j => x (true, j)) -
            cyclicEval f χ (fun j => x (false, j - e)) := cyclicEval_sub (M := M) f χ _ _
      _ = _ := by
        exact congrArg (fun z => cyclicEval f χ (fun j => x (true, j)) - z)
          (cyclicEval_shift f χ e (fun j => x (false, j)))
  have hchar : χ (2 • e) = χ e ^ 2 := by
    simpa [nsmul_eq_mul] using χ.map_nsmul_eq_pow 2 e
  have houter := cyclicEval_sub (M := M) f χ
    (fun j => (ternaryInputStage M e).eval x (false, j))
    (fun j => (ternaryInputStage M e).eval x (false, j - 2 • e))
  have hshift := cyclicEval_shift f χ (2 • e)
    (fun j => (ternaryInputStage M e).eval x (false, j))
  simp only [ternaryRecovery_eval]
  rw [houter, hshift, hfirst, hchar]
  ring

theorem ternaryRecovery_cyclicEval_high {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (χ : AddChar (ZMod M) S) (e : ZMod M)
    (x : Bool × ZMod M → R) :
    cyclicEval f χ (fun j => (ternaryRecovery M e).eval x (true, j)) =
      (1 - χ e ^ 2) *
        (cyclicEval f χ (fun j => x (false, j)) -
          cyclicEval f χ (fun j => x (true, j))) := by
  have hfirst : cyclicEval f χ
      (fun j => (ternaryInputStage M e).eval x (true, j)) =
      cyclicEval f χ (fun j => x (false, j)) -
        cyclicEval f χ (fun j => x (true, j)) := by
    simp only [ternaryInputStage_eval]
    exact cyclicEval_sub (M := M) f χ _ _
  have hchar : χ (2 • e) = χ e ^ 2 := by
    simpa [nsmul_eq_mul] using χ.map_nsmul_eq_pow 2 e
  have houter := cyclicEval_sub (M := M) f χ
    (fun j => (ternaryInputStage M e).eval x (true, j))
    (fun j => (ternaryInputStage M e).eval x (true, j - 2 • e))
  have hshift := cyclicEval_shift f χ (2 • e)
    (fun j => (ternaryInputStage M e).eval x (true, j))
  simp only [ternaryRecovery_eval]
  rw [houter, hshift, hfirst, hchar]
  ring

/-- Algebraic recovery identity used when the two inputs encode `a+b` and
`a+ζb`. The scale `3*d` is retained without cancellation. -/
theorem ternaryRecovery_scaled_identity {S : Type*} [CommRing S]
    (ζ d a b D E : S) (hζ : 1 + ζ + ζ ^ 2 = 0)
    (hD : D = d * (a + b)) (hE : E = d * (a + ζ * b)) :
    (1 - ζ ^ 2) * (E - ζ * D) = 3 * d * a ∧
      (1 - ζ ^ 2) * (D - E) = 3 * d * b := by
  have hζsq : ζ ^ 2 = -1 - ζ := by linear_combination hζ
  have hζcube : ζ ^ 3 = 1 := by
    rw [pow_succ, hζsq]
    have hsum : ζ + ζ ^ 2 = -1 := by rw [hζsq]; ring
    calc
      (-1 - ζ) * ζ = -ζ - ζ ^ 2 := by ring
      _ = 1 := by calc
        -ζ - ζ ^ 2 = -(ζ + ζ ^ 2) := by ring
        _ = -(-1) := by rw [hsum]
        _ = 1 := by ring
  have hfactor : (1 - ζ ^ 2) * (1 - ζ) = 3 := by
    calc
      (1 - ζ ^ 2) * (1 - ζ) = 1 - ζ - ζ ^ 2 + ζ ^ 3 := by ring
      _ = 3 := by
        rw [hζcube]
        have hsum : ζ + ζ ^ 2 = -1 := by rw [hζsq]; ring
        calc
          1 - ζ - ζ ^ 2 + 1 = 2 - (ζ + ζ ^ 2) := by ring
          _ = 3 := by
            calc
              2 - (ζ + ζ ^ 2) = 2 - (-1) := by rw [hsum]
              _ = 3 := by ring
  constructor
  · rw [hD, hE]
    calc
      (1 - ζ ^ 2) * (d * (a + ζ * b) - ζ * (d * (a + b))) =
          d * a * ((1 - ζ ^ 2) * (1 - ζ)) := by ring
      _ = 3 * d * a := by rw [hfactor]; ring
  · rw [hD, hE]
    calc
      (1 - ζ ^ 2) * (d * (a + b) - d * (a + ζ * b)) =
          d * b * ((1 - ζ ^ 2) * (1 - ζ)) := by ring
      _ = 3 * d * b := by rw [hfactor]; ring

end DivisionFree.Fourier
