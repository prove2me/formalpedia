-- Prove2me | Theorems.Thm_ReweightedNPMLE_coordinateLog_lipschitzOn
-- name    : ReweightedNPMLE.coordinateLog_lipschitzOn
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:37:14.565021+00:00
-- url     : https://prove2.me/theorems/5c7bb39b-2c8b-4226-af1d-b5ded33a6788
-- title:
--   Lipschitz continuity of coordinatewise logarithms under a positive lower bound
-- statement:
--   Let $n\ge1$, let $S\subset\mathbb R^n$, and let $\widehat v:\mathbb R^n\to\mathbb R^n$ be $K$-Lipschitz on $S$ in the coordinate sup norm, with $K\ge0$. Suppose $c>0$ and $\widehat v(w)_i\ge c$ for every $w\in S$ and every coordinate. Then the map $z(w)_i=\log(\widehat v(w)_i)$ satisfies
--   $$
--   \|z(w)-z(u)\|_\infty
--   \le\frac{K}{c}\|w-u\|_\infty
--   \qquad(w,u\in S).
--   $$
--   No maximizing property or convexity assumption is required.
--
--   The result isolates the analytic step that transfers fitted-value stability to fitted-log stability for positive models.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L274-L299

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

theorem ReweightedNPMLE.coordinateLog_lipschitzOn {n : ℕ} [Nonempty (Fin n)]
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {K : ℝ≥0} {c : ℝ}
    (hc : 0 < c) (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hlip : LipschitzOnWith K vhat s) :
    LipschitzOnWith ⟨(K : ℝ) / c, by positivity⟩
      (fun w i ↦ Real.log (vhat w i)) s := by sorry
