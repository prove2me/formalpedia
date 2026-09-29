-- Prove2me | Theorems.Thm_WorkbookSource_problem_16025
-- name    : WorkbookSource.problem_16025
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:03:43.158523+00:00
-- url     : https://prove2.me/theorems/7595a4af-0b0c-4215-8669-ec149e77b060
-- title:
--   Solving a pair of linear equations
-- statement:
--   Find the value of $x$ in the system of equations:
--   $2x + y = 5$
--   $x - y = 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16025` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16025; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16025 (x y : ℝ) (h₁ : 2*x + y = 5) (h₂ : x - y = 1) : x = 2 ∧ y = 1  :=  by sorry
