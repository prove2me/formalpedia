-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_convexHull_projection_error
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:15:54.059078+00:00
-- url     : https://prove2.me/submissions/8c651d1e-0aad-4a83-99a5-47d1b4bb4be5

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
import Theorems.Thm_ReweightedNPMLE_gaussian_atom_projection_error

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
/-- The atomwise estimate extends to the entire convex hull, hence to every
Gaussian fitted vector.  This is the analytic content of Proposition 4.1. -/
theorem solution {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    (hv₀ : ∀ i, Real.exp (-(T * S + S ^ 2 / 2)) ≤ v₀ i)
    {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ convexHull ℝ (relativeGaussianAtom x v₀ '' K)) :
    ‖u - (gaussianTaylorSubspace L x v₀).starProjection u‖ ≤
      Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
        (T * S) ^ (L + 1) / (L + 1).factorial) := by
  let V := gaussianTaylorSubspace L x v₀
  let Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.id ℝ _ - V.starProjection
  let eps := Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
    (T * S) ^ (L + 1) / (L + 1).factorial)
  have hconv : Convex ℝ (Q ⁻¹' Metric.closedBall 0 eps) :=
    (convex_closedBall 0 eps).linear_preimage Q.toLinearMap
  have hsubset : relativeGaussianAtom x v₀ '' K ⊆
      Q ⁻¹' Metric.closedBall 0 eps := by
    intro y hy
    rcases hy with ⟨θ, hθK, rfl⟩
    rw [Set.mem_preimage, Metric.mem_closedBall]
    simpa [Q, V, eps, dist_eq_norm] using
      gaussian_atom_projection_error L x v₀ θ hT hS hx (hK θ hθK) hv₀
  have humem : u ∈ Q ⁻¹' Metric.closedBall 0 eps :=
    convexHull_min hsubset hconv hu
  rw [Set.mem_preimage, Metric.mem_closedBall] at humem
  simpa [Q, V, eps, dist_eq_norm] using humem
