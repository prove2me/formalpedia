-- Prove2me | Theorems.Thm_lean_workbook_plus_38118
-- name    : lean_workbook_plus_38118
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/025240de-2360-4911-bfc3-21cc97e10160
-- statement:
--   $\Leftrightarrow \frac{1}{2} \sum_{cyclic}x^2 (y-z)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38118 {x y z : ℝ} : 0 ≤ 1 / 2 * (x ^ 2 * (y - z) ^ 2 + y ^ 2 * (z - x) ^ 2 + z ^ 2 * (x - y) ^ 2)   :=  by sorry
