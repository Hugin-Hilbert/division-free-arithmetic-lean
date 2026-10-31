/- Extracted from the modular-composition formalization; see docs/PROVENANCE.json. -/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

/-!
# Algebra behind truncated-series basis changes and Hensel correction

These statements concern correctness only. They do not assert a running time
or implement a recursive linear-system solver.
-/

namespace DivisionFree.Lifting

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- A matrix congruent to the identity modulo a nilpotent scalar is invertible. -/
theorem isUnit_one_add_smul (t : R) (A : Matrix ι ι R) (L : ℕ) (ht : t ^ L = 0) :
    IsUnit (1 + t • A) := by
  apply IsNilpotent.isUnit_one_add
  refine ⟨L, ?_⟩
  rw [smul_pow, ht, zero_smul]

omit [DecidableEq ι] in
/-- The residual correction identity used at each Hensel recursion node. -/
theorem hensel_correction (G : Matrix ι ι R) (b x₀ x₁ r ε : ι → R)
    (t : R) (q h : ℕ) (hh : h ≤ q) (ht : t ^ q = 0)
    (hresidual : b - G *ᵥ x₀ = t ^ h • r)
    (hcorrection : G *ᵥ x₁ = r + t ^ (q - h) • ε) :
    G *ᵥ (x₀ + t ^ h • x₁) = b := by
  rw [mulVec_add, mulVec_smul, hcorrection, smul_add, smul_smul,
    ← pow_add, Nat.add_sub_of_le hh, ht, zero_smul, add_zero, ← hresidual]
  exact add_sub_cancel _ _

theorem linear_solution_unique (G : Matrix ι ι R) (hG : IsUnit G)
    (x y b : ι → R) (hx : G *ᵥ x = b) (hy : G *ᵥ y = b) : x = y := by
  exact mulVec_injective_of_isUnit hG (hx.trans hy.symm)

/-- A nilpotent perturbation of any invertible matrix is invertible. -/
theorem isUnit_add_smul (H A : Matrix ι ι R) (hH : IsUnit H)
    (t : R) (L : ℕ) (ht : t ^ L = 0) : IsUnit (H + t • A) := by
  obtain ⟨U, rfl⟩ := hH
  have h := U.isUnit.mul (isUnit_one_add_smul t ((↑U⁻¹ : Matrix ι ι R) * A) L ht)
  convert h using 1
  simp [mul_add, ← mul_assoc]

end DivisionFree.Lifting
