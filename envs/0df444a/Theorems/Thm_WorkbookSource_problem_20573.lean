-- Prove2me | Theorems.Thm_WorkbookSource_problem_20573
-- name    : WorkbookSource.problem_20573
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:15.279867+00:00
-- url     : https://prove2.me/theorems/eadb4823-dd58-4b01-810d-249bab03a51e
-- title:
--   A strict chain above one
-- statement:
--   Observe that $y^2+1>y^2>y$ for $y>1$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20573` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20573; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_20573 (y : ℝ) (h₁ : 1 < y) : y^2 + 1 > y^2 ∧ y^2 > y  :=  by sorry
