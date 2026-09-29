-- Prove2me | Theorems.Thm_WorkbookSource_problem_22195
-- name    : WorkbookSource.problem_22195
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:18.413396+00:00
-- url     : https://prove2.me/theorems/34adc97d-6e71-4c4d-8782-54f273ef6329
-- title:
--   Comparing adjacent-base powers
-- statement:
--   Which one is greater $(1000)^{1000}$ or $(1001)^{999}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22195` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22195; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_22195 : (1000 : ℝ) ^ 1000 > 1001 ^ 999  :=  by sorry
