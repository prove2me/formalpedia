-- Prove2me | Theorems.Thm_WorkbookSource_problem_50759
-- name    : WorkbookSource.problem_50759
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:47:56.800973+00:00
-- url     : https://prove2.me/theorems/c0452607-6bb9-439c-9c4e-9cd0849c03c6
-- title:
--   The even integers from zero through117
-- statement:
--   the number of even numbers $k\\in \left [ 0,117 \right ]$ is : $\frac{117+1}{2}=59$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50759` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50759; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_50759 :
  Finset.card (Finset.filter (λ x => Even x) (Finset.range 117)) = 59  :=  by sorry
