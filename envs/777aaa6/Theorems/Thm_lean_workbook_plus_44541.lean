-- Prove2me | Theorems.Thm_lean_workbook_plus_44541
-- name    : lean_workbook_plus_44541
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/bdeab1fe-52af-4433-862a-15bfcb61964c
-- statement:
--   (x - 2)(x + 3) > 0 $\Rightarrow$ x $\in$ ( - $\infty$ , - 3) $\cup$ (2,$\infty$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44541 (x : ℝ) : (x - 2) * (x + 3) > 0 ↔ x < -3 ∨ x > 2   :=  by sorry
