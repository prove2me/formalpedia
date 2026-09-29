-- Prove2me | Theorems.Thm_WorkbookSource_problem_42346
-- name    : WorkbookSource.problem_42346
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:16.165523+00:00
-- url     : https://prove2.me/theorems/4c0c4d3d-cc39-4531-94ab-0b233454e65e
-- title:
--   A fourth degree square identity inequality
-- statement:
--   prove or disprove that for any $x,y$
--    $x^4+25y^4+30x^2y^2 \geq 40xy^3+8x^3y$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42346` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42346; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_42346 (x y : ℝ) : x^4 + 25*y^4 + 30*x^2*y^2 ≥ 40*x*y^3 + 8*x^3*y  :=  by sorry
