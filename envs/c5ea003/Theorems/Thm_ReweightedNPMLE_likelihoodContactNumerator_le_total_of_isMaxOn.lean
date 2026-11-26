-- Prove2me | Theorems.Thm_ReweightedNPMLE_likelihoodContactNumerator_le_total_of_isMaxOn
-- name    : ReweightedNPMLE.likelihoodContactNumerator_le_total_of_isMaxOn
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:36:39.046195+00:00
-- url     : https://prove2.me/theorems/94c29a5c-b66b-42b2-aa4d-a473e3e32989
-- title:
--   Unnormalized likelihood contact inequality at a fitted-value maximizer
-- statement:
--   Let $C\subset(0,\infty)^n$ be convex, let $w\in\mathbb R^n$, and suppose $v\in C$ maximizes the weighted log-likelihood $L_w(u)=\sum_iw_i\log u_i$ over $C$. For every feasible vector $a\in C$,
--   $$
--   \sum_{i=1}^n w_i\frac{a_i}{v_i}\le \sum_{i=1}^n w_i.
--   $$
--   The weights may be arbitrary real numbers; their positivity is not assumed in this unnormalized assertion. All denominators are positive because $v\in C$.
--
--   This first-order contact inequality supplies a supporting linear constraint on the feasible fitted vectors at any attained weighted-likelihood maximum.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedContact.lean#L27-L72

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.likelihoodContactNumerator_le_total_of_isMaxOn
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (ha : a ∈ C) :
    likelihoodContactNumerator w v a ≤ total w := by sorry
