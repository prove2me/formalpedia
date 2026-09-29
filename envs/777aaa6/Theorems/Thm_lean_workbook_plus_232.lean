-- Prove2me | Theorems.Thm_lean_workbook_plus_232
-- name    : lean_workbook_plus_232
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/53370bc7-7155-4748-bd8f-d377c6daa8d9
-- statement:
--   Let $a, b>0$ and $ab+\frac{1}{ab}=6.$ Prove that $(a+1)( b+1) \geq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_232 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b + 1 / (a * b) = 6) : (a + 1) * (b + 1) ≥ 2   :=  by sorry
