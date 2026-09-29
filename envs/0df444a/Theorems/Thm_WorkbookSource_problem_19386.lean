-- Prove2me | Theorems.Thm_WorkbookSource_problem_19386
-- name    : WorkbookSource.problem_19386
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:05:11.322864+00:00
-- url     : https://prove2.me/theorems/606b1c34-dd03-4434-9638-87a1a591b78a
-- title:
--   Solving a strict quadratic inequality
-- statement:
--   Given the inequality $2x^2 + x - 6 < 0$, find the set of $x$-values that satisfy it.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19386` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19386; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_19386 (x : ℝ) : 2 * x ^ 2 + x - 6 < 0 ↔ -2 < x ∧ x < 3/2  :=  by sorry
