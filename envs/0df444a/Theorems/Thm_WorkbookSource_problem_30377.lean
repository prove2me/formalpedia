-- Prove2me | Theorems.Thm_WorkbookSource_problem_30377
-- name    : WorkbookSource.problem_30377
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:58:36.997245+00:00
-- url     : https://prove2.me/theorems/37d32dd2-27c1-4aeb-b6aa-bebf9514849f
-- title:
--   Factoring a quadratic equation
-- statement:
--   Factor the quadratic equation $x^2 - 3x + 2 = 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30377` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30377; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_30377 (x : ℝ) : x^2 - 3*x + 2 = 0 ↔ (x - 1)*(x - 2) = 0  :=  by sorry
