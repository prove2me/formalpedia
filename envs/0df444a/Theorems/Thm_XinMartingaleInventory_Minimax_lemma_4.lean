-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_4
-- name    : XinMartingaleInventory.Minimax.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:00.54386+00:00
-- url     : https://prove2.me/theorems/1bd276c3-963c-44b6-b31d-eadc9f9de956
-- title:
--   Lemma 4 — Continuity and convexity of the explicit objective
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Lemma 4. g^T(x,d) is a continuous and convex function of x on (0,U), and a right (left) continuous function of x at 0 (U).
--
--   Differences from the source:
--   - encoding: real-variable formulas with rational primitives and integer threshold indices → rational A and B cast into real formulas, with finite interval-indicator sums selecting integer indices; reason: the interval selector is unique on the stated domain, including right-closed A intervals, left-closed B intervals through index n, and index minus one
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 4, p.21 (PDF p.21)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_4 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (d : ℝ) (hd : d ∈ Set.Icc 0 (U : ℝ)) :
    ContinuousOn (fun x => explicitG U b T x d) (Set.Ioo 0 (U : ℝ)) ∧
    ConvexOn ℝ (Set.Ioo 0 (U : ℝ)) (fun x => explicitG U b T x d) ∧
    ContinuousWithinAt (fun x => explicitG U b T x d) (Set.Ici 0) 0 ∧
    ContinuousWithinAt (fun x => explicitG U b T x d) (Set.Iic (U : ℝ)) (U : ℝ) := by sorry

end XinMartingaleInventory.Minimax
