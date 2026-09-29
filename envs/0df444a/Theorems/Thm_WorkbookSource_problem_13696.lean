-- Prove2me | Theorems.Thm_WorkbookSource_problem_13696
-- name    : WorkbookSource.problem_13696
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:02:28.486283+00:00
-- url     : https://prove2.me/theorems/818f8b3d-26b8-43fd-8506-931d22fdd6a0
-- title:
--   Sine and cosine of complementary angles
-- statement:
--   Prove that $\sin 70^{\circ} = \cos 20^{\circ}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13696` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13696; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13696 (x : ℝ) : Real.sin (70 * π / 180) = Real.cos (20 * π / 180)  :=  by sorry
