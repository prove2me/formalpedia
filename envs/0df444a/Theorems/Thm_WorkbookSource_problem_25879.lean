-- Prove2me | Theorems.Thm_WorkbookSource_problem_25879
-- name    : WorkbookSource.problem_25879
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:21.146202+00:00
-- url     : https://prove2.me/theorems/0f7f8903-ea9d-4054-8b6c-eb53aefa3dbd
-- title:
--   A greatest common divisor of two Mersenne numbers
-- statement:
--   Find the gcd (greatest common divisor) of $2^{20}-1$ and $2^{110}-1$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25879` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25879; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_25879 :
  Nat.gcd (2^20 - 1) (2^110 - 1) = 1023  :=  by sorry
