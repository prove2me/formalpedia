-- Prove2me | Theorems.Thm_WorkbookSource_problem_18736
-- name    : WorkbookSource.problem_18736
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:04:54.868474+00:00
-- url     : https://prove2.me/theorems/fe2b0ab6-a5f2-4aa7-af3c-14d5106f4a78
-- title:
--   Solving a reflected functional equation
-- statement:
--   Find the closed-form solution $f(x)$ to the equation: $f(x) + 2f(2-x) = 2x(2-x)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18736` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18736; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_18736 (f : ℝ → ℝ) (hf : ∀ x, f x + 2 * f (2 - x) = 2 * x * (2 - x)) : ∀ x, f x = 2 * x * (2 - x) / 3  :=  by sorry
