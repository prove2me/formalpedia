-- Prove2me | Theorems.Thm_WorkbookSource_problem_51028
-- name    : WorkbookSource.problem_51028
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:00.473507+00:00
-- url     : https://prove2.me/theorems/092d058d-7f93-45a9-bb63-61474d84f938
-- title:
--   Simplifying the volume expression of a cylinder
-- statement:
--   Volume of cylinder: $ 2r\cdot r^2\cdot\pi = 2r^3\pi$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51028` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51028; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_51028 (r : ℝ) : 2 * r * (r ^ 2 * π) = 2 * r ^ 3 * π  :=  by sorry
