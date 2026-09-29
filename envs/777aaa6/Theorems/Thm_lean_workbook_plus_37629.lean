-- Prove2me | Theorems.Thm_lean_workbook_plus_37629
-- name    : lean_workbook_plus_37629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ae73dac5-f83c-458a-acd3-1f0b222d68d2
-- statement:
--   From $ab>0$ follows that $a+b \neq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37629 (a b : ℝ) (hab : a * b > 0) : a + b ≠ 0   :=  by sorry
