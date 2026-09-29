-- Prove2me | Theorems.Thm_WorkbookSource_problem_9565
-- name    : WorkbookSource.problem_9565
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:18.282582+00:00
-- url     : https://prove2.me/theorems/77547029-a03e-4f0c-9ddc-8debb18180b3
-- title:
--   The intersection of a unit circle and a tangent line
-- statement:
--   The system of equations:
--    $\begin{cases}x^2+y^2=1 \ 3x+4y=5\end{cases}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9565` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9565; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9565 (x y : ℝ) (h₁ : x ^ 2 + y ^ 2 = 1) (h₂ : 3 * x + 4 * y = 5) : x = 3 / 5 ∧ y = 4 / 5  :=  by sorry
