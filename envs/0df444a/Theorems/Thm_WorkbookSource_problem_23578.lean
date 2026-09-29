-- Prove2me | Theorems.Thm_WorkbookSource_problem_23578
-- name    : WorkbookSource.problem_23578
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:39.647975+00:00
-- url     : https://prove2.me/theorems/fe06e0ac-7599-4f03-a68c-14a288cc2a3b
-- title:
--   A fourth power difference inequality
-- statement:
--   Given $ a, b, c$ are real numbers. Prove that: $ (a - b)^4 + (b - c)^4 + (c - a)^4 \geq\ 8(a - b)^2(c - a)(c - b)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23578` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23578; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_23578 (a b c : ℝ) : (a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4 ≥ 8 * (a - b) ^ 2 * (c - a) * (c - b)  :=  by sorry
