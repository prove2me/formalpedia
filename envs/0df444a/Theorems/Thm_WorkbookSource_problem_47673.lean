-- Prove2me | Theorems.Thm_WorkbookSource_problem_47673
-- name    : WorkbookSource.problem_47673
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:23.032825+00:00
-- url     : https://prove2.me/theorems/b7deb262-7cf0-414a-94b2-561501f64412
-- title:
--   A bound for two numbers in the unit interval
-- statement:
--   If $ a,b\in [0,1]$ then $ a+(b-ab)\geq a\geq 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47673` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47673; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_47673 (a b: ℝ) (ha : 0 <= a ∧ a <= 1) (hb : 0 <= b ∧ b <= 1): a + (b - a*b) >= a ∧ a >= 0  :=  by sorry
