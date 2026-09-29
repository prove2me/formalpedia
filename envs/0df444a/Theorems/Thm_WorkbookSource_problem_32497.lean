-- Prove2me | Theorems.Thm_WorkbookSource_problem_32497
-- name    : WorkbookSource.problem_32497
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:01:49.390518+00:00
-- url     : https://prove2.me/theorems/766524e5-eae7-47ff-90cf-3290e18d5dbb
-- title:
--   Monotonicity of a rational function on nonnegative inputs
-- statement:
--   The 2nd, if $0\le a\le b$ , then $\frac{a}{1+a}\le\frac{b}{1+b}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32497` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32497; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_32497  (a b : ℝ)
  (h₀ : 0 ≤ a ∧ a ≤ b) :
  a / (1 + a) ≤ b / (1 + b)  :=  by sorry
