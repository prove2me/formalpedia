-- Prove2me | Theorems.Thm_WorkbookSource_problem_24006
-- name    : WorkbookSource.problem_24006
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:04.563238+00:00
-- url     : https://prove2.me/theorems/d9b6839b-87ce-4383-8525-8c4aed617125
-- title:
--   A difference of powers divisible by seventeen
-- statement:
--   The nice way (I used) to extract it is by FLT mod 17. $3^{16}\equiv 2^{16}\equiv 1 \pmod{17}$ by Fermat's Little Theorem. So $17|(3^{16}-2^{16})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24006` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24006; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_24006 :
  17 ∣ (3^16 - 2^16)  :=  by sorry
