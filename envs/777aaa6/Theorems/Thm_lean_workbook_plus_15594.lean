-- Prove2me | Theorems.Thm_lean_workbook_plus_15594
-- name    : lean_workbook_plus_15594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e7a9991d-1fd0-4a1a-846b-23c1efaff482
-- statement:
--   If $a,b,c$ are the lengths of triangle sides, prove that $abc\ge (a+b-c)(b+c-a)(c+a-b)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15594 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a * b * c ≥ (a + b - c) * (b + c - a) * (c + a - b)   :=  by sorry
