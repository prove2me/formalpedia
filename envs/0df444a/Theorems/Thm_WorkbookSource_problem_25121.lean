-- Prove2me | Theorems.Thm_WorkbookSource_problem_25121
-- name    : WorkbookSource.problem_25121
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:12.974438+00:00
-- url     : https://prove2.me/theorems/b9c6c09e-7d4c-4c36-9f4a-0753da0c2596
-- title:
--   Factoring one less than a power of two
-- statement:
--   Note that $1023=2^{10}-1\implies1023=(2^5-1)(2^5+1)=31\times33$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25121` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25121; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_25121 :
  1023 = (2^5 - 1) * (2^5 + 1)  :=  by sorry
