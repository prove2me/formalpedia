-- Prove2me | Theorems.Thm_WorkbookSource_problem_7824
-- name    : WorkbookSource.problem_7824
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:03.457494+00:00
-- url     : https://prove2.me/theorems/991ac1ba-5534-4ec7-a228-485576d5d939
-- title:
--   Solving a two-variable linear system
-- statement:
--   Solve the system of equations: $2x-3y+1 = 1$ & $2x+y-3 = 13$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7824` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7824; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_7824 (x y : ℝ) (h₁ : 2*x-3*y+1 = 1) (h₂ : 2*x+y-3 = 13) : x = 6 ∧ y = 4  :=  by sorry
