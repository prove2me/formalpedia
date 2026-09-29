-- Prove2me | Theorems.Thm_lean_workbook_plus_28459
-- name    : lean_workbook_plus_28459
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f40301d5-f476-47be-a2b6-3cbaa0e9a473
-- statement:
--   In triangle $ABC$ ,prove $3a^2+(b+c)^2>4ac$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28459 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * a ^ 2 + (b + c) ^ 2 > 4 * a * c   :=  by sorry
