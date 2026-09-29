-- Prove2me | Theorems.Thm_WorkbookSource_problem_32101
-- name    : WorkbookSource.problem_32101
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:59:07.506115+00:00
-- url     : https://prove2.me/theorems/253833ea-daa6-4178-bccb-80e1cf6f94f8
-- title:
--   An exponential power with logarithmic exponent
-- statement:
--   Given $a=e$ and $b=\ln 2$, both are irrational but $a^b = 2$ which is rational.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32101` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32101; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_32101 : (Real.exp 1) ^ (Real.log 2) = 2  :=  by sorry
