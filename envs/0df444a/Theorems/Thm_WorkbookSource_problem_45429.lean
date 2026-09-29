-- Prove2me | Theorems.Thm_WorkbookSource_problem_45429
-- name    : WorkbookSource.problem_45429
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:53.956296+00:00
-- url     : https://prove2.me/theorems/02e38eb3-6e43-465f-9519-d7dc1e405842
-- title:
--   The greatest element of a five-value set
-- statement:
--   If $ a=-2$ , the largest number in the set $ \\left \\{ -3a,4a,\\frac{24}{a},a^2,1 \\right \\}$ is
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45429` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45429; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_45429 (a : ℝ) (h : a = -2) : 
  IsGreatest ({-3*a, 4*a, 24/a, a^2, 1} : Set ℝ) 6  :=  by sorry
