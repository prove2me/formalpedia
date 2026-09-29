-- Prove2me | Theorems.Thm_lean_workbook_plus_20196
-- name    : lean_workbook_plus_20196
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/cfd20f43-d7c2-4089-ab3b-740e10eb736f
-- statement:
--   Let $a+b+c=0$ . Prove that $(ab)^2+(bc)^2+(ac)^2+6abc \ge -3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20196 (a b c : ℝ) (hab : a + b + c = 0) : (a * b) ^ 2 + (b * c) ^ 2 + (a * c) ^ 2 + 6 * a * b * c ≥ -3   :=  by sorry
