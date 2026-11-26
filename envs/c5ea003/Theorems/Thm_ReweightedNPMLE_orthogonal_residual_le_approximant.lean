-- Prove2me | Theorems.Thm_ReweightedNPMLE_orthogonal_residual_le_approximant
-- name    : ReweightedNPMLE.orthogonal_residual_le_approximant
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:47:14.383914+00:00
-- url     : https://prove2.me/theorems/0d13fccf-d5ee-5007-9eca-0ff58adf06a4
-- title:
--   Best-approximation inequality for orthogonal projection
-- statement:
--   Let $V\subset\mathbb R^n$ be a linear subspace and $P_V$ its orthogonal projection. For every $x\in\mathbb R^n$ and $y\in V$, $$\|x-P_Vx\|_2\le\|x-y\|_2.$$ This allows an explicit Taylor approximant to bound the orthogonal residual.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianWidth.lean#L41-L58

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

theorem ReweightedNPMLE.orthogonal_residual_le_approximant {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (x y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) :
    ‖x - V.starProjection x‖ ≤ ‖x - y‖ := by sorry
