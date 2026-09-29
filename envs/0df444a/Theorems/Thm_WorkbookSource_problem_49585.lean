-- Prove2me | Theorems.Thm_WorkbookSource_problem_49585
-- name    : WorkbookSource.problem_49585
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:08:47.850374+00:00
-- url     : https://prove2.me/theorems/1ea34ec4-829e-44ea-bdf3-53b79c34aa68
-- title:
--   Dividing a strict angle bound
-- statement:
--   Given the restriction $3x < π$, find the valid range for $x$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49585` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49585; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_49585 (x : ℝ) (h : 3 * x < π) : x < π / 3  :=  by sorry
