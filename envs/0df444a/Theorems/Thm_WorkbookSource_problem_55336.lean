-- Prove2me | Theorems.Thm_WorkbookSource_problem_55336
-- name    : WorkbookSource.problem_55336
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:56.508672+00:00
-- url     : https://prove2.me/theorems/98106a3c-5c31-4e34-9e3e-a6252ff91b4a
-- title:
--   A cubic inequality on the nonnegative reals
-- statement:
--   Prove that $x^3+15x\ge 7x^2$ for all $x\ge 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55336` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55336; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_55336 (x : ℝ) (hx : 0 ≤ x) : x ^ 3 + 15 * x ≥ 7 * x ^ 2  :=  by sorry
