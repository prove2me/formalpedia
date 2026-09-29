-- Prove2me | Theorems.Thm_lean_workbook_plus_23339
-- name    : lean_workbook_plus_23339
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f64cf167-42a5-4cc4-b6ac-2486e8051469
-- statement:
--   Given that real numbers $a, b$ satisfy the following\n$a^3-3a^2+5a-17=0$\nb^3-3b^2+5b+11=0$\nFind the value of $a+b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23339 (a b : ℝ) (ha : a^3 - 3*a^2 + 5*a - 17 = 0) (hb : b^3 - 3*b^2 + 5*b + 11 = 0) : a + b = 2   :=  by sorry
