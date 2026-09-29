-- Prove2me | Theorems.Thm_WorkbookSource_problem_57253
-- name    : WorkbookSource.problem_57253
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:03:39.618162+00:00
-- url     : https://prove2.me/theorems/3aaaadd1-9273-44a4-becd-e9e811c8203c
-- title:
--   A strict product inequality with unit sum
-- statement:
--   Prove that if $a, b, c > 0$ and $a + b + c = 1$, then $ab + bc + ca > 2abc$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57253` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. This statement gives a strict inequality; the related record plus_16237 has a non-strict bound.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57253; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_57253 (a b c : ℝ) (habc : a + b + c = 1) (h : a > 0 ∧ b > 0 ∧ c > 0) : a * b + b * c + c * a > 2 * a * b * c  :=  by sorry
