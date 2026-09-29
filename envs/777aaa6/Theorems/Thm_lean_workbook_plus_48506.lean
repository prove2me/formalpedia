-- Prove2me | Theorems.Thm_lean_workbook_plus_48506
-- name    : lean_workbook_plus_48506
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/cc04c8f0-3884-4d0a-9f15-cce753917b53
-- statement:
--   Prove that $(a+b-2c)^4+(a+c-2b)^4+(b+c-2a)^4\geq9((a-b)^4+(a-c)^4+(b-c)^4)).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48506 (a b c : ℝ) : (a + b - 2 * c) ^ 4 + (a + c - 2 * b) ^ 4 + (b + c - 2 * a) ^ 4 ≥ 9 * ((a - b) ^ 4 + (a - c) ^ 4 + (b - c) ^ 4)   :=  by sorry
