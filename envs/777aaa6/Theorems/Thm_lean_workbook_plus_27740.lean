-- Prove2me | Theorems.Thm_lean_workbook_plus_27740
-- name    : lean_workbook_plus_27740
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/e72008d1-88fe-4091-82f6-25b90aba32f2
-- statement:
--   $\sqrt{\frac{15}{2} \cdot \frac{1}{2} \cdot \frac{9}{2} \cdot \frac{5}{2}}=\frac{15}{4} \sqrt{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27740 (x : ℝ) (hx : x = 15 / 2 * 1 / 2 * 9 / 2 * 5 / 2) : Real.sqrt x = 15 / 4 * Real.sqrt 3   :=  by sorry
