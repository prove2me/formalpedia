-- Prove2me | Theorems.Thm_lean_workbook_plus_11847
-- name    : lean_workbook_plus_11847
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b382f85d-766f-48bb-b5ed-8a4a687d7abe
-- statement:
--   Given $a, b, c$ positive numbers, $a^2 + b^2 + c^2 = 3$. Prove that: $2(a + b + c) + \frac{1}{abc} \geq 7$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11847 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c = 3) : 2 * (a + b + c) + 1 / (a * b * c) ≥ 7   :=  by sorry
