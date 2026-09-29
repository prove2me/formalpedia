-- Prove2me | Theorems.Thm_WorkbookSource_problem_9982
-- name    : WorkbookSource.problem_9982
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:32.253832+00:00
-- url     : https://prove2.me/theorems/9ec475e0-df1c-43d6-af40-f35c7624b87d
-- title:
--   Evaluating a specified quadratic function at one
-- statement:
--   Evaluate $f(x)=x^2+x$ at $x=1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9982` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9982; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9982 (f : ℝ → ℝ) (x : ℝ) (f_def : f = fun x => x^2 + x) : f 1 = 2  :=  by sorry
