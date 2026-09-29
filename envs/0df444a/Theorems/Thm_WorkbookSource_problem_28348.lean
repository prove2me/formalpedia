-- Prove2me | Theorems.Thm_WorkbookSource_problem_28348
-- name    : WorkbookSource.problem_28348
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:38.670725+00:00
-- url     : https://prove2.me/theorems/72248bd9-add2-4bac-9684-c557b509208e
-- title:
--   Continuity of the sine of a sum of coordinate squares
-- statement:
--   Show regoriously that the function $\sin(x^2+y^2)$ is continuous at $(0,0)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28348` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28348; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_28348 (x y : ℝ) : Continuous fun p : ℝ × ℝ => sin (p.1^2 + p.2^2)  :=  by sorry
