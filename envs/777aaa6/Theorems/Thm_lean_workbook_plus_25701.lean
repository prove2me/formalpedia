-- Prove2me | Theorems.Thm_lean_workbook_plus_25701
-- name    : lean_workbook_plus_25701
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/cf248b89-a23e-40a7-b4e0-f3ae7a983d43
-- statement:
--   If a,b,c are the sidelengths of triangle, prove that $(a+b)(b+c)(c+a)\geq 8(a+b-c)(b+c-a)(c+a-b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25701 b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :  (a + b) * (b + c) * (c + a) >= 8 * (a + b - c) * (b + c - a) * (c + a - b)   :=  by sorry
