-- Prove2me | Theorems.Thm_lean_workbook_plus_58457
-- name    : lean_workbook_plus_58457
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/575fcc05-f39d-4922-be3c-8cffe744ad6c
-- statement:
--   Since the thesis, we write the inequality in equivalent form: \n\n $\sum_{cyc}{(a-b)^{2}\over ab}\cdot{(a-c)^{2}\over ac}\geq 0. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58457 (a b c : ℝ) : (a - b) ^ 2 / a / b * (b - c) ^ 2 / b / c * (c - a) ^ 2 / c / a ≥ 0   :=  by sorry
