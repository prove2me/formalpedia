-- Prove2me | Theorems.Thm_WorkbookSource_problem_28817
-- name    : WorkbookSource.problem_28817
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:56.256256+00:00
-- url     : https://prove2.me/theorems/e67c4343-7a8d-4c17-84a5-8e430cf508ce
-- title:
--   Evaluating a ratio of three products
-- statement:
--   Calculate $\frac{20\times 22\times 24}{10\times 11 \times 12}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28817` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28817; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_28817 (a : ℚ) (h : a = 20 * 22 * 24 / (10 * 11 * 12)) : a = 8  :=  by sorry
