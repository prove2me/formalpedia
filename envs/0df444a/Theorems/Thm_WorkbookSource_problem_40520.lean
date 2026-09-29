-- Prove2me | Theorems.Thm_WorkbookSource_problem_40520
-- name    : WorkbookSource.problem_40520
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:04.800017+00:00
-- url     : https://prove2.me/theorems/212ab044-92b6-4622-a792-cd6b556f67e5
-- title:
--   Evaluating a rational expression at ninety
-- statement:
--   For a real number $x=90$,
--
--   $$\frac{2x-4+x}{23x+2}=\frac{19}{148}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40520` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40520; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_40520 (x : ℝ) (hx : x = 90) : (2 * x - 4 + x) / (23 * x + 2) = 19 / 148  :=  by sorry
