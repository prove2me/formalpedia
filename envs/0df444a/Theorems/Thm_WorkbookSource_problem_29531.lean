-- Prove2me | Theorems.Thm_WorkbookSource_problem_29531
-- name    : WorkbookSource.problem_29531
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:36:54.071202+00:00
-- url     : https://prove2.me/theorems/b5982e20-c345-4560-af9a-f6efd142a51c
-- title:
--   A triple evaluation of a linear recurrence
-- statement:
--   Find $f(f(f(5)))$ given $f(x) = f(x-1) + 4$ and $f(0) = 3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29531` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29531; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_29531 (f : ℤ → ℤ) (h₁ : ∀ x, f x = f (x - 1) + 4) (h₂ : f 0 = 3) : f (f (f 5)) = 383  :=  by sorry
