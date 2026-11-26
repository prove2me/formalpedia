-- Prove2me | Theorems.Thm_ReweightedNPMLE_strictConcaveOn_weightedLogLikelihood
-- name    : ReweightedNPMLE.strictConcaveOn_weightedLogLikelihood
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:14.972049+00:00
-- url     : https://prove2.me/theorems/cf2c7cb8-8763-415b-a9b8-71ef07289f1c
-- title:
--   Strict concavity of positively weighted finite log likelihood
-- statement:
--   Write $L_w(v)=\sum_iw_i\log v_i$. For $n\ge1$ and strictly positive weights $w_i$, the function $L_w$ is strictly concave on $(0,\infty)^n$. Thus for distinct positive vectors $x,y$ and $a,b>0$ with $a+b=1$, $$aL_w(x)+bL_w(y)<L_w(ax+by).$$ This establishes uniqueness of fitted values without imposing uniqueness of their mixing-law representations.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Weights.lean#L50-L88

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.strictConcaveOn_weightedLogLikelihood {n : ℕ} [Nonempty (Fin n)]
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) :
    StrictConcaveOn ℝ (positiveVectors n) (weightedLogLikelihood w) := by sorry
