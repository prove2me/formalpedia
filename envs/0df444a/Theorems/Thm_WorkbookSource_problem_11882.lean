-- Prove2me | Theorems.Thm_WorkbookSource_problem_11882
-- name    : WorkbookSource.problem_11882
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:39.803054+00:00
-- url     : https://prove2.me/theorems/f20ac57f-d284-44c9-8536-555d8a107cbf
-- title:
--   A strict pair-product bound above one
-- statement:
--   For $a,b,c>1$ then $ab+bc+ca>3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11882` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11882; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_11882 (a b c : ℝ) (hab : 1 < a) (hbc : 1 < b) (hca : 1 < c) : a * b + b * c + c * a > 3  :=  by sorry
