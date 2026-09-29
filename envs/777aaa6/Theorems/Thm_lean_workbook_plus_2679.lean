-- Prove2me | Theorems.Thm_lean_workbook_plus_2679
-- name    : lean_workbook_plus_2679
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/565d37c4-c88a-4522-8dd6-856df956a080
-- statement:
--   Prove that $1+\frac{1}{1!}+\frac{1}{2!}+\frac{1}{3!}+...<3$ without using calculus.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2679 : ∑' n : ℕ, (1 / (n + 1)! ) < 3   :=  by sorry
