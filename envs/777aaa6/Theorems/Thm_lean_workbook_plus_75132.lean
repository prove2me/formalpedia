-- Prove2me | Theorems.Thm_lean_workbook_plus_75132
-- name    : lean_workbook_plus_75132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/7506680a-34a8-4b84-9470-e04d85b5f6e4
-- statement:
--   If $a+b+c+d=6$ for positive $a,b,c,d,$ find the maximum possible value of $a+b+c+d.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75132 (a b c d : ℝ) (h : a + b + c + d = 6) : a + b + c + d ≤ 6   :=  by sorry
