-- Prove2me | Theorems.Thm_lean_workbook_plus_12283
-- name    : lean_workbook_plus_12283
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/cb8f7a8d-01e8-4169-a7fb-3a5c408db403
-- statement:
--   If a,b,c are side lengths of triangle , prove that $(a+b)(a+c)(b+c) \geq 8(a+b-c)(a+c-b)(b+c-a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12283 b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :  (a + b) * (a + c) * (b + c) >= 8 * (a + b - c) * (a + c - b) * (b + c - a)   :=  by sorry
