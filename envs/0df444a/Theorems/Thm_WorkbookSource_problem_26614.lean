-- Prove2me | Theorems.Thm_WorkbookSource_problem_26614
-- name    : WorkbookSource.problem_26614
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:24.69589+00:00
-- url     : https://prove2.me/theorems/091b03c5-90ec-4636-946c-851537afb092
-- title:
--   Nonnegativity of a cyclic reciprocal sum
-- statement:
--   Prove that if a,b,c > 0 and abc=1, then
--    $\frac{1}{(a+b+1)} + \frac{1}{(b+c+1)} + \frac{1}{(c+a+1)}\geq0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26614` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26614; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_26614 (a b c : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
  1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 0  :=  by sorry
