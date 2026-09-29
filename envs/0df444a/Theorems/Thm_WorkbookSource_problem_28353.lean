-- Prove2me | Theorems.Thm_WorkbookSource_problem_28353
-- name    : WorkbookSource.problem_28353
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:50.409234+00:00
-- url     : https://prove2.me/theorems/bc9b32ef-2f4f-49ab-8788-5c0d87341757
-- title:
--   A cubic bound on a closed interval
-- statement:
--   Prove that $a^3\ge 3a-2$ for all $2\ge a \ge -2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28353` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28353; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_28353 (a : ℝ) (h1: a ≥ -2 ∧ a ≤ 2) : a^3 ≥ 3*a - 2  :=  by sorry
