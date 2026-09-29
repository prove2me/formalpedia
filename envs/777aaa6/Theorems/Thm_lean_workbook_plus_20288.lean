-- Prove2me | Theorems.Thm_lean_workbook_plus_20288
-- name    : lean_workbook_plus_20288
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7563ebf1-49fd-48e4-b33b-2bdc0d3a79c9
-- statement:
--   Demonstrate the inequality $(b-c)^2+(c-a)^2\ge\frac12(a-b)^2$ using the inequality $x^2+y^2\ge\frac12(x+y)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20288 (a b c : ℝ) : (b - c) ^ 2 + (c - a) ^ 2 ≥ 1 / 2 * (a - b) ^ 2   :=  by sorry
