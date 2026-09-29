-- Prove2me | Theorems.Thm_WorkbookSource_problem_12277
-- name    : WorkbookSource.problem_12277
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:44.227728+00:00
-- url     : https://prove2.me/theorems/bf083f6d-c1cb-4a5b-bf57-1c6326f63d19
-- title:
--   A sixth-degree nonnegative polynomial
-- statement:
--   Simplify and prove the inequality after squaring both sides:
--   $$(a-1)^2(9a^4-84a^3+310a^2-580a+601)\geq0$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12277` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12277; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_12277 : ∀ a : ℝ, (a - 1) ^ 2 * (9 * a ^ 4 - 84 * a ^ 3 + 310 * a ^ 2 - 580 * a + 601) ≥ 0  :=  by sorry
