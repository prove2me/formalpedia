-- Prove2me | Theorems.Thm_ReweightedNPMLE_fitted_maximizer_firstOrder_nonpos
-- name    : ReweightedNPMLE.fitted_maximizer_firstOrder_nonpos
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:36:52.007638+00:00
-- url     : https://prove2.me/theorems/4e6f5645-5c24-585a-9e3b-633f359de786
-- title:
--   Variational inequality for a positive fitted-value maximizer
-- statement:
--   Let $n\ge1$, let $C\subset(0,\infty)^n$ be convex, and let $w\in\mathbb R^n$. Suppose $v\in C$ maximizes $L_w(u)=\sum_iw_i\log u_i$ over $C$. Then every feasible comparison vector $a\in C$ satisfies
--   $$
--   \sum_{i=1}^n w_i\frac{a_i-v_i}{v_i}\le0.
--   $$
--   The weights are not required to be positive; positivity of the fitted vectors ensures that the fractions and logarithmic derivatives are well defined.
--
--   This inequality expresses nonpositive first-order improvement along every feasible chord. Comparing it at two optimizers yields quantitative stability bounds for the fitted-vector map.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L42-L60

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

theorem ReweightedNPMLE.fitted_maximizer_firstOrder_nonpos {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ) (hv : IsMaxOn C (weightedLogLikelihood w) v)
    (ha : a ∈ C) :
    ∑ i, w i * ((a i - v i) / v i) ≤ 0 := by sorry
