-- Prove2me | Theorems.Thm_lean_workbook_plus_64968
-- name    : lean_workbook_plus_64968
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f8b97ed3-38a5-4080-8288-d3f1b265e3be
-- statement:
--   $\Leftrightarrow \frac{3 (x - 1)^2 (-3 x^{10} + 34 x^9 - 157 x^8 + 444 x^7 - 1061 x^6 + 1970 x^5 - 1803 x^4 + 256 x^3 + 216 x^2 + 144 x +216)}{8x^4(3-x)^4} \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64968 : ∀ x : ℝ, (3 * (x - 1) ^ 2 * (-3 * x ^ 10 + 34 * x ^ 9 - 157 * x ^ 8 + 444 * x ^ 7 - 1061 * x ^ 6 + 1970 * x ^ 5 - 1803 * x ^ 4 + 256 * x ^ 3 + 216 * x ^ 2 + 144 * x + 216)) / (8 * x ^ 4 * (3 - x) ^ 4) ≥ 0   :=  by sorry
