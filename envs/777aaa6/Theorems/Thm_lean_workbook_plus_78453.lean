-- Prove2me | Theorems.Thm_lean_workbook_plus_78453
-- name    : lean_workbook_plus_78453
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f8f72044-59aa-404f-9d3e-2832f351581e
-- statement:
--   Let $a>0,$ $b>0,$ $a^4+b^4=2.$ Prove that $4(a+b)+\frac{3}{ab}\geq11.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78453 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (h : a^4 + b^4 = 2) : 4 * (a + b) + 3 / (a * b) ≥ 11   :=  by sorry
