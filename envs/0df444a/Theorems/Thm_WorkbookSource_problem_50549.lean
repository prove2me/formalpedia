-- Prove2me | Theorems.Thm_WorkbookSource_problem_50549
-- name    : WorkbookSource.problem_50549
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:52.437514+00:00
-- url     : https://prove2.me/theorems/5e236404-de47-45c5-8040-4968a80b34a8
-- title:
--   Solving two symmetric linear equations
-- statement:
--   Solve the systems of equations graphically.
--
--   $y=3x-1$
--   $x=3y-1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50549` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50549; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_50549 (x y : ℝ) (h₁ : y = 3 * x - 1) (h₂ : x = 3 * y - 1) : x = 1 / 2 ∧ y = 1 / 2  :=  by sorry
