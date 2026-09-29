-- Prove2me | Theorems.Thm_WorkbookSource_problem_14193
-- name    : WorkbookSource.problem_14193
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:03:40.028807+00:00
-- url     : https://prove2.me/theorems/dbc5165d-86c8-4083-a943-2ae2e0fdb07c
-- title:
--   Evaluating an involutive reciprocal functional equation
-- statement:
--   Find $f(6)$ using the equation $2f(x) + 3f\\left(\\frac{2010}{x}\\right) = 5x$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14193` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14193; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_14193 (f : ℝ → ℝ) (hf : ∀ x, 2 * f x + 3 * f (2010 / x) = 5 * x) : f 6 = 993  :=  by sorry
