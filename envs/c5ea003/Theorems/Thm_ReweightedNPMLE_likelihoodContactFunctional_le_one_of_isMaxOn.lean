-- Prove2me | Theorems.Thm_ReweightedNPMLE_likelihoodContactFunctional_le_one_of_isMaxOn
-- name    : ReweightedNPMLE.likelihoodContactFunctional_le_one_of_isMaxOn
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:37:22.085261+00:00
-- url     : https://prove2.me/theorems/c7d8e27f-7344-44df-aeac-0b7e1597027a
-- title:
--   Normalized likelihood contact hyperplane bounds every feasible fitted vector
-- statement:
--   Let $n\ge1$, let $C\subset(0,\infty)^n$ be convex, and let every weight $w_i$ be strictly positive. Suppose $v\in C$ maximizes $L_w(u)=\sum_iw_i\log u_i$ over $C$. With $W=\sum_iw_i$, define the linear contact functional
--   $$
--   \Lambda_{w,v}(a)=\frac1W\sum_{i=1}^n w_i\frac{a_i}{v_i}.
--   $$
--   Then every $a\in C$ satisfies
--   $$
--   \Lambda_{w,v}(a)\le1.
--   $$
--   The normalizing factor is positive since the index set is nonempty and all weights are positive.
--
--   This normalized supporting inequality provides the contact hyperplane used to identify active atoms of likelihood-maximizing mixtures.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedContact.lean#L103-L123

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

theorem ReweightedNPMLE.likelihoodContactFunctional_le_one_of_isMaxOn
    {n : ℕ} [Nonempty (Fin n)] {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (ha : a ∈ C) :
    likelihoodContactFunctional w v a ≤ 1 := by sorry
