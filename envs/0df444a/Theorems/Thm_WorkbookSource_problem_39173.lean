-- Prove2me | Theorems.Thm_WorkbookSource_problem_39173
-- name    : WorkbookSource.problem_39173
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:19.043757+00:00
-- url     : https://prove2.me/theorems/94e44d0c-6766-4960-898c-a8bcf1d976e0
-- title:
--   A strict product bound for integers above two
-- statement:
--   Prove that if $a, b$ are integers and $a, b>2$ , then $ab>a+b$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39173` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. This is a strict integer bound; the related record plus_53847 gives a non-strict real inequality under a different premise.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39173; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_39173 (a b : ℤ) (h₁ : 2 < a) (h₂ : 2 < b) : a * b > a + b  :=  by sorry
