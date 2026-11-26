-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_atom_projection_error
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:15:02.789685+00:00
-- url     : https://prove2.me/submissions/2f43f660-537f-4936-8c4a-81a37c591eef

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
import Theorems.Thm_ReweightedNPMLE_euclidean_norm_le_sqrt_card_mul
import Theorems.Thm_ReweightedNPMLE_gaussianTaylorAtom_coordinate_error
import Theorems.Thm_ReweightedNPMLE_orthogonal_residual_le_approximant

-- Inline helpers preserved from ReweightedNPMLE.GaussianWidth.
section
/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

namespace ReweightedNPMLE







/-! ## The concrete Gaussian Taylor subspace -/









/-- The Taylor subspace contains the all-one vector. -/
theorem one_mem_gaussianTaylorSubspace {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) :
    WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)) ∈
      gaussianTaylorSubspace L x v₀ := by
  apply Submodule.subset_span
  exact ⟨none, rfl⟩







theorem gaussianTaylorApproximant_mem {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) :
    gaussianTaylorApproximant L x v₀ θ ∈ gaussianTaylorSubspace L x v₀ := by
  apply Submodule.sub_mem
  · apply Submodule.sum_mem
    intro m _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨some m, rfl⟩
  · exact one_mem_gaussianTaylorSubspace L x v₀











end ReweightedNPMLE
end

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
/-- Residual-width bound for every individual Gaussian atom. -/
theorem solution {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hθ : ‖θ‖ ≤ S)
    (hv₀ : ∀ i, Real.exp (-(T * S + S ^ 2 / 2)) ≤ v₀ i) :
    ‖relativeGaussianAtom x v₀ θ -
        (gaussianTaylorSubspace L x v₀).starProjection
          (relativeGaussianAtom x v₀ θ)‖ ≤
      Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
        (T * S) ^ (L + 1) / (L + 1).factorial) := by
  let eps := Real.exp (2 * T * S + S ^ 2 / 2) *
    (T * S) ^ (L + 1) / (L + 1).factorial
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  exact (orthogonal_residual_le_approximant
    (gaussianTaylorSubspace L x v₀) (relativeGaussianAtom x v₀ θ)
      (gaussianTaylorApproximant L x v₀ θ)
      (gaussianTaylorApproximant_mem L x v₀ θ)).trans
    (euclidean_norm_le_sqrt_card_mul
      (relativeGaussianAtom x v₀ θ - gaussianTaylorApproximant L x v₀ θ)
      heps (fun i ↦ by
        simpa [eps] using
          gaussianTaylorAtom_coordinate_error L x v₀ θ hT hS hx hθ hv₀ i))
