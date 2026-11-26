-- Prove2me | Theorems.Thm_ReweightedNPMLE_fittedLog_monotone
-- name    : ReweightedNPMLE.fittedLog_monotone
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:13.216917+00:00
-- url     : https://prove2.me/theorems/31c99cca-d6c1-5eab-942c-c059c1c69a9d
-- title:
--   Monotonicity of selected fitted log-vectors in the likelihood weights
-- statement:
--   Let $n\ge1$, let $C,S\subset\mathbb R^n$, and suppose $\widehat v(w)\in C$ maximizes $\sum_iw_i\ell(v_i)$ over $C$ for every $w\in S$. Set $\ell(x)=\log|x|$ for $x\ne0$ and $\ell(0)=0$, and write $z(w)_i=\ell(\widehat v(w)_i)$. For any $w,u\in S$,
--   $$
--   \sum_{i=1}^n(w_i-u_i)\bigl(z(w)_i-z(u)_i\bigr)\ge0.
--   $$
--   Neither convexity of $C$ or $S$ nor positivity of the weights is assumed. The maximizing selections need not be unique.
--
--   This monotonicity property follows solely from comparing attained optima and supplies the nonnegative quadratic-form limit used in fitted-likelihood Hessian analysis.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L62-L85

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

theorem ReweightedNPMLE.fittedLog_monotone {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)}
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    ∀ w ∈ s, ∀ u ∈ s,
      0 ≤ ∑ i, (w i - u i) *
        (Real.log (vhat w i) - Real.log (vhat u i)) := by sorry
