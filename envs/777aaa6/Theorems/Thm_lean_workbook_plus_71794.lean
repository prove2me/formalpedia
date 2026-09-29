-- Prove2me | Theorems.Thm_lean_workbook_plus_71794
-- name    : lean_workbook_plus_71794
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c93d58b2-04e4-457a-b109-09ac5dbc02d8
-- statement:
--   Now, we know (from the Triangle Inequality): $a < b+c$ $b < a+c$ $c < a+b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71794 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a < b + c ∧ b < a + c ∧ c < a + b   :=  by sorry
