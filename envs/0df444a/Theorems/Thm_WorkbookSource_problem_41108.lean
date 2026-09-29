-- Prove2me | Theorems.Thm_WorkbookSource_problem_41108
-- name    : WorkbookSource.problem_41108
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:23.652016+00:00
-- url     : https://prove2.me/theorems/5cc6a97c-e1f4-4a4f-add0-d65fab75cdef
-- title:
--   An exact binomial quotient
-- statement:
--   The following rational quotient has exact value
--
--   $$\frac{56\cdot7+35\cdot8}{\binom{15}{4}}=\frac{32}{65}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41108` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41108; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_41108 :
  ((56 * 7 + 35 * 8) : ℚ) / (choose 15 4 : ℚ) = 32 / 65  :=  by sorry
