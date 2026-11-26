-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_local_positive_weight_lower_bound
-- name    : ReweightedNPMLE.exists_local_positive_weight_lower_bound
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:38:03.268238+00:00
-- url     : https://prove2.me/theorems/f5f20448-9dfd-5406-abd9-45d1b7b76b47
-- title:
--   A common positive coordinate bound near a positive weight vector
-- statement:
--   Let $w\in\mathbb R^n$ have strictly positive coordinates. There exist a real number $a>0$ and a neighborhood $U$ of $w$ such that
--   $$
--   u_i\ge a
--   \qquad\text{for every }u\in U\text{ and every coordinate }i.
--   $$
--   The same constant works for all coordinates and all weights in the neighborhood; only finiteness of the coordinate index set is used. The conclusion remains meaningful when the index set is empty.
--
--   This local uniform bound permits estimates with reciprocal weight factors to be applied throughout a neighborhood of any positive weight vector.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L359-L377

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

theorem ReweightedNPMLE.exists_local_positive_weight_lower_bound {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ a : ℝ, 0 < a ∧ ∃ s : Set (Fin n → ℝ),
      s ∈ nhds w ∧ ∀ u ∈ s, ∀ i, a ≤ u i := by sorry
