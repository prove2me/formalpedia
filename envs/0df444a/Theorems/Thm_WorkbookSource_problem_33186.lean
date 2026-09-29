-- Prove2me | Theorems.Thm_WorkbookSource_problem_33186
-- name    : WorkbookSource.problem_33186
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:22:14.860071+00:00
-- url     : https://prove2.me/theorems/ca9a6c1a-22b1-45fb-ba22-54784fbabb95
-- title:
--   The norm of an integer power of a complex number
-- statement:
--   For every complex number z and integer n, ‖zⁿ‖=‖z‖ⁿ.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33186` (Apache-2.0). The complete source proposition and variable types are retained.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33186; Apache-2.0

import Mathlib
open Complex

theorem WorkbookSource.problem_33186 (z : ℂ) (n : ℤ) : ‖z^n‖ = ‖z‖^n  :=  by sorry
