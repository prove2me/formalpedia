-- Prove2me | Theorems.Thm_WorkbookSource_problem_23850
-- name    : WorkbookSource.problem_23850
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:51:57.724752+00:00
-- url     : https://prove2.me/theorems/9a69a790-e11e-49bb-b5b4-5e32dbcc4e9b
-- title:
--   Solving a quadratic expression for y
-- statement:
--   For, $x=a \longrightarrow 2a-3y+z^2=1 \longrightarrow y=\frac{1}{3}z^2+\frac{2a-1}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23850` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23850; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_23850 (x y z a : ℝ) (h₁ : x = a) (h₂ : 2 * a - 3 * y + z ^ 2 = 1) : y = 1 / 3 * z ^ 2 + (2 * a - 1) / 3  :=  by sorry
