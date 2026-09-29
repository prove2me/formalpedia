-- Prove2me | Theorems.Thm_WorkbookSource_problem_39879
-- name    : WorkbookSource.problem_39879
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:04.774986+00:00
-- url     : https://prove2.me/theorems/433dee6a-e9ed-401c-8e64-05c1f32a748b
-- title:
--   A nonnegative sixth degree polynomial
-- statement:
--   Let $x\geq 0$ ,prove that: $3.x^6+2x+2x^2+x^3-x^4-2x^5\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39879` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39879; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_39879 (x : ℝ) (hx: x >= 0) : 3 * x^6 + 2 * x + 2 * x^2 + x^3 - x^4 - 2 * x^5 >= 0  :=  by sorry
