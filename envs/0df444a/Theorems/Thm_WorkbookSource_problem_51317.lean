-- Prove2me | Theorems.Thm_WorkbookSource_problem_51317
-- name    : WorkbookSource.problem_51317
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:58.383498+00:00
-- url     : https://prove2.me/theorems/f512db79-00f1-454e-b4ad-a2490329593e
-- title:
--   Completing a quadratic square
-- statement:
--   Let's consider $ 4A^2+8A+1$ alone. Factoring out $ 4$ gives $ 4(A^2+2A+1/4)$ . Completing the square: $ 4(A^2+2A+3/4+1/4)-3=4(A+1)^2-3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51317` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51317; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_51317  (a : ℝ) :
  4 * a^2 + 8 * a + 1 = 4 * (a + 1)^2 - 3  :=  by sorry
