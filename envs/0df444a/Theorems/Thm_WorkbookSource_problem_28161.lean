-- Prove2me | Theorems.Thm_WorkbookSource_problem_28161
-- name    : WorkbookSource.problem_28161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:44.281457+00:00
-- url     : https://prove2.me/theorems/847bdb9f-3cb7-475b-84f1-05f3d21883a6
-- title:
--   A factorial quotient for repeated letters
-- statement:
--   basically arranging $D UUU RRR $ , which is $\frac{7!}{3! 3!} = \boxed{140}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28161` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_28161 :
  7! / (3! * 3!) = 140  :=  by sorry
