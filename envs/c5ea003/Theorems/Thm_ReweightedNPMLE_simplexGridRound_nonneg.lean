-- Prove2me | Theorems.Thm_ReweightedNPMLE_simplexGridRound_nonneg
-- name    : ReweightedNPMLE.simplexGridRound_nonneg
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:19.259095+00:00
-- url     : https://prove2.me/theorems/2c5c168b-0e51-5d46-8398-440b27cae4f3
-- title:
--   Nonnegativity of rounded simplex weights
-- statement:
--   For $w\in\mathbb R^{k+1}$ and integer $M\ge0$, define $r_i=\lfloor Mw_i\rfloor_+/M$ for the first $k$ coordinates and $r_{k+1}=1-\sum_{i=1}^k r_i$, where the floor is truncated below at zero and division at $M=0$ is zero. If $M>0$, every $w_i\ge0$, and $\sum_iw_i=1$, then $$r_i\ge0\quad\text{for every }i.$$ Together with exact mass preservation, this proves that the rounded vector is again a probability weight vector.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SimplexGrid.lean#L80-L105

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

theorem ReweightedNPMLE.simplexGridRound_nonneg {k M : ℕ} (hM : 0 < M)
    (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwsum : ∑ i, w i = 1) (i : Fin (k + 1)) :
    0 ≤ simplexGridRound k M w i := by sorry
