-- Prove2me | Theorems.Thm_WorkbookSource_problem_39351
-- name    : WorkbookSource.problem_39351
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:39:56.25066+00:00
-- url     : https://prove2.me/theorems/9109641e-db78-4dd9-80b3-4c5a7705c360
-- title:
--   The square of the imaginary unit
-- statement:
--   For the imaginary unit $i\in\mathbb C$,
--
--   $$i\cdot i=-1.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39351` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39351; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_39351 :
  Complex.I * Complex.I = -1  :=  by sorry
