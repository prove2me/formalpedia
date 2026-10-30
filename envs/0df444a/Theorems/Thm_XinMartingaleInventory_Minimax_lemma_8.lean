-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_8
-- name    : XinMartingaleInventory.Minimax.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:19.691991+00:00
-- url     : https://prove2.me/theorems/bf06bb07-212f-4812-9eb3-9f4922a15785
-- title:
--   Lemma 8 — Convex-concave continuation geometry
-- statement:
--   Standing setting: positive rational U,b, integer T≥1. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Lemma 8. For each fixed x ∈ [0,U], ḡ^T(x,d) is a continuous function of d on (0,U), and a right (left) - continuous function of d at 0 (U). Also, ḡ^T(x,d) is a convex function of d on (0,z^T_x), and a concave function of d on (z^T_x,U).
--
--   Differences from the source:
--   - encoding: real-variable formulas with rational primitives and integer threshold indices → rational A and B cast into real formulas, with finite interval-indicator sums selecting integer indices; reason: the interval selector is unique on the stated domain, including right-closed A intervals, left-closed B intervals through index n, and index minus one
--   - encoding: z is the infimum over nonnegative d where the threshold is defined → take the infimum within [0,U]; reason: d=U is feasible and no d>U can decrease the infimum; the source formulas are defined on [0,U]
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 8, p.22 (PDF p.22)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_8 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 1 ≤ T) (x : ℝ) (hx : x ∈ Set.Icc 0 (U : ℝ)) :
    ContinuousOn (continuation U b T x) (Set.Ioo 0 (U : ℝ)) ∧
    ContinuousWithinAt (continuation U b T x) (Set.Ici 0) 0 ∧
    ContinuousWithinAt (continuation U b T x) (Set.Iic (U : ℝ)) (U : ℝ) ∧
    ConvexOn ℝ (Set.Ioo 0 (crossing U b T x)) (continuation U b T x) ∧
    ConcaveOn ℝ (Set.Ioo (crossing U b T x) (U : ℝ)) (continuation U b T x) := by sorry

end XinMartingaleInventory.Minimax
