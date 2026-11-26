-- Prove2me | solution 1 for ReweightedNPMLE.orthogonal_residual_le_approximant
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:13:28.183+00:00
-- url     : https://prove2.me/submissions/a73540ea-2e0e-478a-ab67-88da25ca95f5

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

/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Orthogonal projection has no larger residual than any supplied subspace approximant. -/
theorem solution {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) :
    ‖x - V.starProjection x‖ ≤ ‖x - y‖ := by
  have hproj_y : V.orthogonal.starProjection y = 0 := by
    rw [Submodule.starProjection_apply,
      Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
        (V.le_orthogonal_orthogonal hy)]
    rfl
  calc
    ‖x - V.starProjection x‖ = ‖V.orthogonal.starProjection x‖ := by
      have hopen := DFunLike.congr_fun (Submodule.starProjection_orthogonal V) x
      change V.orthogonal.starProjection x = x - V.starProjection x at hopen
      exact congrArg norm hopen.symm
    _ = ‖V.orthogonal.starProjection (x - y)‖ := by
      rw [map_sub, hproj_y, sub_zero]
    _ ≤ ‖x - y‖ := V.orthogonal.norm_starProjection_apply_le _
