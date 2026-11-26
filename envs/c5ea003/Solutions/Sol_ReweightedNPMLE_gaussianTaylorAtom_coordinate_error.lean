-- Prove2me | solution 1 for ReweightedNPMLE.gaussianTaylorAtom_coordinate_error
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:13:54.622303+00:00
-- url     : https://prove2.me/submissions/b952a32b-2ca2-44ee-a77b-aae10ac45949

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Theorems.Thm_ReweightedNPMLE_gaussianTaylorApproximant_apply
import Theorems.Thm_ReweightedNPMLE_real_exp_taylor_remainder_bound

/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

open ReweightedNPMLE







/-! ## The concrete Gaussian Taylor subspace -/
open ReweightedNPMLE in
/-- Exact coordinatewise Taylor error with the constant from Proposition 4.1. -/
theorem solution {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hθ : ‖θ‖ ≤ S)
    (hv₀ : ∀ i, Real.exp (-(T * S + S ^ 2 / 2)) ≤ v₀ i) (i : Fin n) :
    |relativeGaussianAtom x v₀ θ i -
        gaussianTaylorApproximant L x v₀ θ i| ≤
      Real.exp (2 * T * S + S ^ 2 / 2) *
        (T * S) ^ (L + 1) / (L + 1).factorial := by
  let A : ℝ := T * S
  let trunc : ℝ := ∑ ell ∈ Finset.range (L + 1),
    (inner ℝ (x i) θ) ^ ell / ell.factorial
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hinner : |inner ℝ (x i) θ| ≤ A := by
    exact (abs_real_inner_le_norm (x i) θ).trans
      (mul_le_mul (hx i) hθ (norm_nonneg θ) hT)
  have hrem : |Real.exp (inner ℝ (x i) θ) - trunc| ≤
      Real.exp A * A ^ (L + 1) / (L + 1).factorial := by
    exact real_exp_taylor_remainder_bound L hA hinner
  have hvpos : 0 < v₀ i :=
    (Real.exp_pos (-(T * S + S ^ 2 / 2))).trans_le (hv₀ i)
  have hinv : (v₀ i)⁻¹ ≤ Real.exp (T * S + S ^ 2 / 2) := by
    calc
      (v₀ i)⁻¹ = 1 / v₀ i := by simp [one_div]
      _ ≤ 1 / Real.exp (-(T * S + S ^ 2 / 2)) :=
        one_div_le_one_div_of_le (Real.exp_pos _) (hv₀ i)
      _ = Real.exp (T * S + S ^ 2 / 2) := by
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring
  have heNeg : Real.exp (-‖θ‖ ^ 2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖θ‖]
  have hscore : Real.exp (gaussianScore (x i) θ) =
      Real.exp (-‖θ‖ ^ 2 / 2) * Real.exp (inner ℝ (x i) θ) := by
    rw [gaussianScore, ← Real.exp_add]
    congr 1
    ring
  have hdiff : relativeGaussianAtom x v₀ θ i -
      gaussianTaylorApproximant L x v₀ θ i =
        Real.exp (-‖θ‖ ^ 2 / 2) *
          (Real.exp (inner ℝ (x i) θ) - trunc) / v₀ i := by
    rw [relativeGaussianAtom, PiLp.toLp_apply,
      gaussianTaylorApproximant_apply, hscore]
    dsimp [trunc]
    ring
  rw [hdiff]
  calc
    |Real.exp (-‖θ‖ ^ 2 / 2) *
        (Real.exp (inner ℝ (x i) θ) - trunc) / v₀ i| =
        Real.exp (-‖θ‖ ^ 2 / 2) *
          |Real.exp (inner ℝ (x i) θ) - trunc| * (v₀ i)⁻¹ := by
            rw [abs_div, abs_mul, Real.abs_exp, abs_of_pos hvpos]
            simp [div_eq_mul_inv]
    _ ≤ 1 * (Real.exp A * A ^ (L + 1) / (L + 1).factorial) *
        Real.exp (T * S + S ^ 2 / 2) := by
          gcongr
    _ = Real.exp (2 * T * S + S ^ 2 / 2) *
        (T * S) ^ (L + 1) / (L + 1).factorial := by
          dsimp [A]
          rw [one_mul, show 2 * T * S + S ^ 2 / 2 =
            T * S + (T * S + S ^ 2 / 2) by ring]
          simp only [Real.exp_add]
          ring
