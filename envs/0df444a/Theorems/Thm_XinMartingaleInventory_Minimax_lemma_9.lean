-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_9
-- name    : XinMartingaleInventory.Minimax.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:05.712019+00:00
-- url     : https://prove2.me/theorems/de210443-57fa-4e3f-91f9-74091b521d91
-- title:
--   Lemma 9 — Geometry of the next-stage objective
-- statement:
--   Standing setting: positive rational U,b, integer T≥2. Inventory primitives and operational demands are rational; the analytical variables in Lemmas 4–9 and 11 range over the displayed real intervals.
--
--   Lemma 9. For each fixed x ∈ [0,U], f^T(x,d) is a continuous function of d on (0,U), and a right (left) - continuous function of d at 0 (U). Also, for all j ∈ [−1,T−2], f^T(x,d) is a convex function of d on (A^T_j,A^T_{j+1}). Furthermore, f^T(x,d) is a convex function of d on (0,𝒜^T_x), and a concave function of d on (α^T_x,U).
--
--   Differences from the source:
--   - encoding: real-variable formulas with rational primitives and integer threshold indices → rational A and B cast into real formulas, with finite interval-indicator sums selecting integer indices; reason: the interval selector is unique on the stated domain, including right-closed A intervals, left-closed B intervals through index n, and index minus one
--   - encoding: z is the infimum over nonnegative d where the threshold is defined → take the infimum within [0,U]; reason: d=U is feasible and no d>U can decrease the infimum; the source formulas are defined on [0,U]
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 9, p.22 (PDF p.22)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_9 (U b : ℚ) (hU : 0 < U) (hb : 0 < b) (T : ℕ) (hT : 2 ≤ T) (x : ℝ) (hx : x ∈ Set.Icc 0 (U : ℝ)) :
    ContinuousOn (nextObjective U b T x) (Set.Ioo 0 (U : ℝ)) ∧
    ContinuousWithinAt (nextObjective U b T x) (Set.Ici 0) 0 ∧
    ContinuousWithinAt (nextObjective U b T x) (Set.Iic (U : ℝ)) (U : ℝ) ∧
    (∀ j : ℤ, -1 ≤ j → j ≤ (T : ℤ)-2 →
      ConvexOn ℝ (Set.Ioo (A U b T j : ℝ) (A U b T (j+1) : ℝ)) (nextObjective U b T x)) ∧
    ConvexOn ℝ (Set.Ioo 0 (geomA U b T x)) (nextObjective U b T x) ∧
    ConcaveOn ℝ (Set.Ioo (alpha U b T x) (U : ℝ)) (nextObjective U b T x) := by sorry

end XinMartingaleInventory.Minimax
