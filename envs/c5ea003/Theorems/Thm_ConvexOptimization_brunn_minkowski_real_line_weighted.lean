-- Prove2me | Theorems.Thm_ConvexOptimization_brunn_minkowski_real_line_weighted
-- name    : ConvexOptimization.brunn_minkowski_real_line_weighted
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T06:13:30.115354+00:00
-- url     : https://prove2.me/theorems/a9fc6856-8ca4-47e2-be6a-89a51f31608a
-- title:
--   Weighted Brunn-Minkowski inequality on the real line
-- statement:
--   Let $0<\lambda<1$, and let $A,B\subseteq\mathbb R$ be nonempty Lebesgue-measurable sets. Their weighted Minkowski sum satisfies
--   $$
--   (1-\lambda)\,\operatorname{vol}(A)+\lambda\,\operatorname{vol}(B)
--   \le \operatorname{vol}\bigl((1-\lambda)A+\lambda B\bigr).
--   $$
--   This is the one-dimensional Brunn–Minkowski inequality used as the geometric input in the first layer-cake proof of the Prékopa–Leindler inequality.
--   **Formalization Note** Measures take values in the extended nonnegative reals. On the right, `volume` evaluates the outer measure of the sum even when that sum has not separately been proved measurable; this removes the source sum-measurability side condition. The source notes that its boundedness assumption is inessential, and the formal theorem omits it.
-- source:
--   R. J. Gardner, The Brunn-Minkowski Inequality, https://faculty.gardner.wwu.edu/gorizia12.pdf, Theorem 2.1, equation (2), PDF p. 3; see also the compact-approximation proof there and the remarks immediately following the theorem that boundedness is inessential and the Minkowski sum may be nonmeasurable.

import Mathlib

open scoped RealInnerProductSpace ENNReal Pointwise
open MeasureTheory Set

theorem ConvexOptimization.brunn_minkowski_real_line_weighted
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) :
    ENNReal.ofReal (1 - l) * volume A + ENNReal.ofReal l * volume B ≤
      volume ((1 - l) • A + l • B) := by
  sorry
