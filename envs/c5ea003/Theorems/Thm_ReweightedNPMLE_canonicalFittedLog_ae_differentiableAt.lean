-- Prove2me | Theorems.Thm_ReweightedNPMLE_canonicalFittedLog_ae_differentiableAt
-- name    : ReweightedNPMLE.canonicalFittedLog_ae_differentiableAt
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:37:32.856851+00:00
-- url     : https://prove2.me/theorems/fab12bab-51d3-57af-afdc-4e2c4b729ed1
-- title:
--   Almost-everywhere differentiability of the canonical fitted-log map
-- statement:
--   Let $n\ge1$ and let $C\subset(0,\infty)^n$ be nonempty, compact, and convex. Choose a maximizer $\widehat v(w)$ of $\sum_iw_i\log v_i$ over $C$ at each real weight vector, and let $z(w)_i=\log(\widehat v(w)_i)$. Then
--   $$
--   z\text{ is Fréchet differentiable at Lebesgue-almost every }
--   w\in(0,\infty)^n.
--   $$
--   For positive weights, strict concavity makes the fitted maximizer unique, so the map there does not depend on arbitrary choices.
--
--   No differentiability hypothesis on the optimizer is assumed. The result supplies the almost-everywhere derivative needed to apply Jacobian and change-of-variables arguments to canonical fitted likelihoods.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L386-L420

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.canonicalFittedLog_ae_differentiableAt
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) :
    ∀ᵐ w ∂volume, w ∈ positiveVectors n →
      DifferentiableAt ℝ (fittedLogSelection C hCcompact hCnonempty hCpos) w := by sorry
