-- Prove2me | Theorems.Thm_lean_workbook_plus_27888
-- name    : lean_workbook_plus_27888
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b5bcfbea-ca28-4292-9cff-4d190c317868
-- statement:
--   Prove: $ |a|+|b|+|c|+|a+b+c|\geq |a+b|+|a+c|+|b+c| $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27888 (a b c : ℝ) : abs a + abs b + abs c + abs (a + b + c) ≥ abs (a + b) + abs (a + c) + abs (b + c)   :=  by sorry
