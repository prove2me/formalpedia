-- Prove2me | Theorems.Thm_ReweightedNPMLE_fittedValue_lipschitzOn
-- name    : ReweightedNPMLE.fittedValue_lipschitzOn
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:37:12.846825+00:00
-- url     : https://prove2.me/theorems/788da35e-e558-5b82-b32d-e675faa1d0d9
-- title:
--   Quantitative Lipschitz bound for fitted-value maximizers
-- statement:
--   Let $n\ge1$, let $C\subset(0,\infty)^n$ be convex, and let $S\subset\mathbb R^n$ be any weight set. Suppose $\widehat v(w)$ maximizes $\sum_iw_i\log v_i$ over $C$ for every $w\in S$. Let $a,c,B>0$ satisfy, for all $w\in S$ and coordinates $i$,
--   $$
--   w_i\ge a,\qquad c\le\widehat v(w)_i\le B.
--   $$
--   Then the fitted-vector selection is Lipschitz on $S$ in the coordinate sup norm:
--   $$
--   \|\widehat v(w)-\widehat v(u)\|_\infty
--   \le \frac{nB^2}{ac}\|w-u\|_\infty
--   \qquad(w,u\in S).
--   $$
--   The coordinate bounds are required only for the selected maximizers.
--
--   This estimate supplies explicit local regularity without differentiating the optimizer map.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedRegularity.lean#L87-L239

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

theorem ReweightedNPMLE.fittedValue_lipschitzOn {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ w ∈ s, ∀ i, a ≤ w i)
    (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hvB : ∀ w ∈ s, ∀ i, vhat w i ≤ B)
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    LipschitzOnWith
      ⟨(n : ℝ) * B ^ 2 / (a * c), by positivity⟩ vhat s := by sorry
