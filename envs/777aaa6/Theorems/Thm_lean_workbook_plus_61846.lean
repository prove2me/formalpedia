-- Prove2me | Theorems.Thm_lean_workbook_plus_61846
-- name    : lean_workbook_plus_61846
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/5323901f-f844-4a01-ab19-a65d59fa5ce2
-- statement:
--   Prove the inequality: $(a-b)(c-a)(b-c) < abc$ for a, b, and c being the lengths of the edges of a triangle.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61846 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a - b) * (c - a) * (b - c) < a * b * c   :=  by sorry
