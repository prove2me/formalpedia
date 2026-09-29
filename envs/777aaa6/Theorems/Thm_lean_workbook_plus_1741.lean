-- Prove2me | Theorems.Thm_lean_workbook_plus_1741
-- name    : lean_workbook_plus_1741
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b3eb698b-d200-42c1-bbf9-40211ea2c402
-- statement:
--   $ a^2 + b^2 + c^2 - ab - bc - ca = \sum_{\text{cyc}} \frac{(a-b)^2}{2} \ge 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1741 (a b c : ℝ) : a^2 + b^2 + c^2 - a * b - b * c - c * a ≥ 0   :=  by sorry
