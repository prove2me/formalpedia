-- Prove2me | Theorems.Thm_WorkbookSource_problem_51808
-- name    : WorkbookSource.problem_51808
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:40.141623+00:00
-- url     : https://prove2.me/theorems/cb1479f8-9430-4f33-bcb8-8154645862b3
-- title:
--   A cubic inequality above two
-- statement:
--   Prove that $x^3+1 > 2x^2$ for $x \ge 2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51808` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. The related Open record plus_25755 omits the variable declaration; this source explicitly declares a real variable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51808; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_51808 (x : ℝ) (h : x >= 2) : x^3 + 1 > 2 * x^2  :=  by sorry
