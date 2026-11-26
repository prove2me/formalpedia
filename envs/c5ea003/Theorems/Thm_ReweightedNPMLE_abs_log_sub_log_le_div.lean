-- Prove2me | Theorems.Thm_ReweightedNPMLE_abs_log_sub_log_le_div
-- name    : ReweightedNPMLE.abs_log_sub_log_le_div
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:27.205799+00:00
-- url     : https://prove2.me/theorems/4cfe6a52-08a0-4189-8850-274021d121c6
-- title:
--   Uniform Lipschitz bound for the logarithm above a positive threshold
-- statement:
--   Let $c,x,y\in\mathbb R$ satisfy $c>0$, $x\ge c$, and $y\ge c$. Then
--   $$
--   |\log x-\log y|\le\frac{|x-y|}{c}.
--   $$
--   Thus the ordinary logarithm is $1/c$-Lipschitz on the entire interval $[c,\infty)$. The bound is symmetric in $x$ and $y$ and remains valid when they coincide.
--
--   This elementary estimate converts quantitative control of positive fitted values into control of their logarithms. Its constant depends only on the common lower bound, so no upper bound on the two arguments is needed.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L241-L272

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

theorem ReweightedNPMLE.abs_log_sub_log_le_div {c x y : ℝ}
    (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by sorry
