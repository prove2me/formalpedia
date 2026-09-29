-- Prove2me | Theorems.Thm_WorkbookSource_problem_39372
-- name    : WorkbookSource.problem_39372
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:39:57.25898+00:00
-- url     : https://prove2.me/theorems/8c80e618-777e-4fbb-ad3d-53105e0f8bf1
-- title:
--   Determining a function value from a linear equation
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ satisfy $4f(-1)=2f(-1)+2$. Then
--
--   $$f(-1)=1.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39372` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39372; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_39372 (f : ℝ → ℝ) (h : 4 * f (-1) = 2 * f (-1) + 2) : f (-1) = 1  :=  by sorry
