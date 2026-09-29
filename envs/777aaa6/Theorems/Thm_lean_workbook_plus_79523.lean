-- Prove2me | Theorems.Thm_lean_workbook_plus_79523
-- name    : lean_workbook_plus_79523
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1d0beebf-35c5-4e46-91dd-4d7c08823faa
-- statement:
--   Let $a,b>0$ and $(a+\frac{1}{b})(b+\frac{1}{a})=5.$ Prove that $$ a+b\geq \sqrt5-1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79523 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : (a + 1/b) * (b + 1/a) = 5) : a + b ≥ Real.sqrt 5 - 1   :=  by sorry
