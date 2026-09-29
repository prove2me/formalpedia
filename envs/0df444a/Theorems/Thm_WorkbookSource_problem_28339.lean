-- Prove2me | Theorems.Thm_WorkbookSource_problem_28339
-- name    : WorkbookSource.problem_28339
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:40:48.555968+00:00
-- url     : https://prove2.me/theorems/7f9083f9-7350-422b-b304-d2585ddace67
-- title:
--   A lower bound involving a square root
-- statement:
--   Prove that $x^2 +2\sqrt{x+2}-3x \geq 2$ for $x\geq 2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28339` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28339; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_28339 (x : ℝ) (h : x ≥ 2) : x^2 + 2 * Real.sqrt (x + 2) - 3 * x ≥ 2  :=  by sorry
