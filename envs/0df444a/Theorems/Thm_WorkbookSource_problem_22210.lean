-- Prove2me | Theorems.Thm_WorkbookSource_problem_22210
-- name    : WorkbookSource.problem_22210
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:43.59424+00:00
-- url     : https://prove2.me/theorems/f0c893df-d83f-4cf0-82d2-002fdb8d0de7
-- title:
--   Positivity of a sixth degree polynomial
-- statement:
--   If $0\leq a\leq 1$ prove that $ 64 a^6 - 192 a^5 + 176 a^4 - 32 a^3 + 116 a^2 - 132 a + 223>0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22210` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22210; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_22210 (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) : 64 * a ^ 6 - 192 * a ^ 5 + 176 * a ^ 4 - 32 * a ^ 3 + 116 * a ^ 2 - 132 * a + 223 > 0  :=  by sorry
