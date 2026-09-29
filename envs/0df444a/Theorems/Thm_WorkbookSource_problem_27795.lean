-- Prove2me | Theorems.Thm_WorkbookSource_problem_27795
-- name    : WorkbookSource.problem_27795
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:49.646772+00:00
-- url     : https://prove2.me/theorems/b8ead1b6-7b19-4f42-932c-f9b408e8a49b
-- title:
--   Sum of cubes from sum and product
-- statement:
--   If $x+y=5$ and $xy=2$ then what is $x^3+y^3$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27795` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27795; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_27795 (x y : ℝ) (h₁ : x + y = 5) (h₂ : x * y = 2) : x^3 + y^3 = 95  :=  by sorry
