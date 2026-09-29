-- Prove2me | Theorems.Thm_WorkbookSource_problem_16351
-- name    : WorkbookSource.problem_16351
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:03:56.742733+00:00
-- url     : https://prove2.me/theorems/22211d28-6c27-4306-9b5f-c9ff63560222
-- title:
--   Recovering two numbers from their sum and difference
-- statement:
--   Solve for $a$ and $b$:
--   $a + b = 6$
--   $a - b = 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16351` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16351; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_16351 (a b : ℝ) : a + b = 6 ∧ a - b = 4 ↔ a = 5 ∧ b = 1  :=  by sorry
