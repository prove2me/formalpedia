-- Prove2me | Theorems.Thm_WorkbookSource_problem_3002
-- name    : WorkbookSource.problem_3002
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:35.875687+00:00
-- url     : https://prove2.me/theorems/7ddc3981-beb2-4797-aa19-dc976fccdc14
-- title:
--   Solving an affine strict inequality
-- statement:
--   Solve the inequality. \\(x+1\dfrac{1}{2}>0\\)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3002` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3002; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_3002 (x : ℝ) : x + 1.5 > 0 ↔ x > -1.5  :=  by sorry
