-- Prove2me | Theorems.Thm_ReweightedNPMLE_simplexGridRound_mem_simplexWeightGrid
-- name    : ReweightedNPMLE.simplexGridRound_mem_simplexWeightGrid
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:12.979337+00:00
-- url     : https://prove2.me/theorems/c7de5afb-68db-495d-8f6c-2afbd8827bc4
-- title:
--   Simplex rounding lies in the explicit finite weight grid
-- statement:
--   For $w\in\mathbb R^{k+1}$ and integer $M\ge0$, define $r_i=\lfloor Mw_i\rfloor_+/M$ for the first $k$ coordinates and $r_{k+1}=1-\sum_{i=1}^k r_i$, where the floor is truncated below at zero and division at $M=0$ is zero. Let $\mathcal G_{k,M}$ be the finite set of vectors $(a_1/M,\ldots,a_k/M,1-\sum_{i=1}^k a_i/M)$ with integers $0\le a_i\le M$, using total division when $M=0$. If $w_i\ge0$ and $\sum_iw_i=1$, then $$r\in\mathcal G_{k,M}.$$ The statement includes $M=0$ and supplies a concrete finite index for every rounded mixture.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SimplexGrid.lean#L249-L271

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Finite simplex-grid rounding

The deterministic denominator-grid construction used to discretize the
Carathéodory mixture weights in the likelihood net.
-/

open scoped BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.simplexGridRound_mem_simplexWeightGrid {k M : ℕ}
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) :
    simplexGridRound k M w ∈ simplexWeightGrid k M := by sorry
