-- Prove2me | Theorems.Thm_WorkbookSource_problem_53725
-- name    : WorkbookSource.problem_53725
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:47.86605+00:00
-- url     : https://prove2.me/theorems/dd964b71-5eef-42ad-9da2-9a858252eda8
-- title:
--   A strict square-root bound
-- statement:
--   Given $n > \frac{25}{12}$, prove that $\sqrt{n(n+2)} > n + \frac{5}{6}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53725` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53725; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_53725 (n : ℝ) (h : n > 25 / 12) : Real.sqrt (n * (n + 2)) > n + 5 / 6  :=  by sorry
