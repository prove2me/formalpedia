-- Prove2me | Theorems.Thm_lean_workbook_plus_72082
-- name    : lean_workbook_plus_72082
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f5c5dc7e-58f3-40c7-a2e1-401879228322
-- statement:
--   Prove that the solution to the equation $\cos(x) = x$ is the limit of the sequence $a_{n+1} = \cos(a_n)$, where $a_0$ is any real number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72082 (a : ℕ → ℝ) (a0 : ℝ) (ha : a = fun n => cos (a (n-1))) : ∃ x, a n = x   :=  by sorry
