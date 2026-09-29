-- Prove2me | Theorems.Thm_WorkbookSource_problem_7831
-- name    : WorkbookSource.problem_7831
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:45:53.483524+00:00
-- url     : https://prove2.me/theorems/70098e72-0e91-42dc-8070-01a20a9e4196
-- title:
--   Comparing two large powers using small bases
-- statement:
--   Which is bigger, $2^{3000}$ or $3^{2000}$? Assume no calculators and no logarithm tables.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7831` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7831; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_7831 : (2^3000:ℝ) < 3^2000  :=  by sorry
