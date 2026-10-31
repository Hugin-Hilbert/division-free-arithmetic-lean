import DivisionFree.Polynomial.TernaryFullMultiplication
import DivisionFree.IntegerBezout

/-! Unconditional quasi-linear full polynomial multiplication over arbitrary
commutative rings. Integer constants are explicit bounded Bézout coefficients.
The bilinear and fixed-factor interfaces are proved in separate modules. -/

namespace DivisionFree.PolynomialArithmetic

open Fourier

universe u

/-- Combine the actual prime-power circuits, cancelling their coprime integer
scales by a fixed integer linear combination of the full coefficient vectors. -/
noncomputable def fastFullMultiplier (n : ℕ) : FullMultiplier.{u} n :=
  if hn : 1 ≤ n then
    combineScaledFullMultipliers
      (primePowerFullMultiplier 2 n Nat.prime_two hn)
      (ternaryFullMultiplier n hn)
      (twoThreeBounded_identity
        (primePowerScale (paddedExponent 2 n)) (primePowerScale (paddedExponent 3 n)))
  else fullSchoolbook n

theorem fastFullMultiplier_correct {R : Type u} [CommRing R]
    (n : ℕ) (x : Bool × Fin n → R) :
    vectorPolynomial (2 * n) ((fastFullMultiplier.{u} n).circuit.eval x) =
      vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i)) :=
  (fastFullMultiplier.{u} n).correct R x

/-- The total signed binary size of every integer leaf in the constructed
full multiplier is also quasi-linear; these constants are not hidden parameters. -/
theorem fastFullMultiplier_constantBits_le (n : ℕ) :
    (fastFullMultiplier n).circuit.constantBits ≤ 30 * n * (Nat.log 2 (2 * n) + 1) := by
  by_cases hn : 1 ≤ n
  · rw [fastFullMultiplier, dif_pos hn, combineScaledFullMultipliers_constantBits,
      primePowerFullMultiplier_constantBits, ternaryFullMultiplier_constantBits,
      Nat.zero_add]
    let a := primePowerScale (paddedExponent 2 n)
    let b := primePowerScale (paddedExponent 3 n)
    have hu := twoThreeBoundedU_size_le a b
    have hv := twoThreeBoundedV_size_le a b
    have ha := primePowerScale_le (paddedExponent 2 n)
    have hb := primePowerScale_le (paddedExponent 3 n)
    have h2 := paddedExponent_logBound (p := 2) (by decide) hn
    have h3 := paddedExponent_logBound (p := 3) (by decide) hn
    have h2pos := paddedExponent_ge_two 2 n
    have h3pos := paddedExponent_ge_two 3 n
    have hbits : (twoThreeBoundedU a b).natAbs.size +
        (twoThreeBoundedV a b).natAbs.size + 2 ≤ 15 * (Nat.log 2 (2 * n) + 1) := by
      dsimp [a, b] at hu hv ⊢
      omega
    calc
      2 * n * ((twoThreeBoundedU a b).natAbs.size +
          (twoThreeBoundedV a b).natAbs.size + 2) ≤
          2 * n * (15 * (Nat.log 2 (2 * n) + 1)) := Nat.mul_le_mul_left (2 * n) hbits
      _ = _ := by ring
  · have hn0 : n = 0 := by omega
    subst n
    simp [fastFullMultiplier, fullSchoolbook, fullSchoolbookCircuit,
      paddingCircuit, schoolbook, Circuit.constantBits]

end DivisionFree.PolynomialArithmetic
