-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_3
-- name    : XinMartingaleInventory.Minimax.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:56:09.049102+00:00
-- url     : https://prove2.me/theorems/8a982e33-21be-47e8-9810-2819e79a9d13
-- title:
--   Lemma 3 — Convexity from the right derivative
-- statement:
--   Lemma 3 (Royden and Fitzpatrick [110]). A one-dimensional function f(x), which is con-
--   tinuous and right-diﬀerentiable on an open interval (a,b) with non-decreasing right-derivative on
--   (a,b), is convex on (a,b).
--
--   Differences from the source:
--   - encoding: a finite right derivative exists and is nondecreasing → a function D records the right derivative via HasDerivWithinAt on the right ray; reason: existence of the right derivative is equivalent to such a derivative function on the interval
--   - encoding: a function defined on the stated interval → a total real function whose values and hypotheses are used only on that interval; reason: every function on the interval has such an extension and all conclusions depend only on its restriction
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 3, p.21 (PDF p.21)

import Mathlib

namespace XinMartingaleInventory.Minimax

theorem lemma_3 (a c : ℝ) (f D : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Ioo a c))
    (hderiv : ∀ x ∈ Set.Ioo a c, HasDerivWithinAt f (D x) (Set.Ioi x) x)
    (hmono : MonotoneOn D (Set.Ioo a c)) : ConvexOn ℝ (Set.Ioo a c) f := by sorry

end XinMartingaleInventory.Minimax
