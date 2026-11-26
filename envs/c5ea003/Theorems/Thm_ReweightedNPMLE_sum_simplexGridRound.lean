-- Prove2me | Theorems.Thm_ReweightedNPMLE_sum_simplexGridRound
-- name    : ReweightedNPMLE.sum_simplexGridRound
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:32.310044+00:00
-- url     : https://prove2.me/theorems/fef20339-02f3-44db-9dfb-d0e13066225b
-- title:
--   Exact mass preservation by simplex-grid rounding
-- statement:
--   For $w\in\mathbb R^{k+1}$ and integer $M\ge0$, define $r_i=\lfloor Mw_i\rfloor_+/M$ for the first $k$ coordinates and $r_{k+1}=1-\sum_{i=1}^k r_i$, where the floor is truncated below at zero and division at $M=0$ is zero. For every input vector, without a positivity or unit-sum assumption, $$\sum_{i=1}^{k+1}r_i=1.$$ This algebraic identity is the mass-preservation component of the finite weight-grid construction.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SimplexGrid.lean#L66-L78

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

theorem ReweightedNPMLE.sum_simplexGridRound {k M : ℕ} (w : Fin (k + 1) → ℝ) :
    ∑ i, simplexGridRound k M w i = 1 := by sorry
