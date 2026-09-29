-- Prove2me | Theorems.Thm_lean_workbook_plus_27177
-- name    : lean_workbook_plus_27177
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/79a83454-e016-4f61-8546-e67e73e777b4
-- statement:
--   Solve the following equation: \n $\cos 2x-\cos 8x+\cos 6x=1$ \n $\iff$ $(\cos 2x-1)(2\cos 2x+1)\cos 4x=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27177 : ∀ x : ℝ, (Real.cos 2*x - Real.cos 8*x + Real.cos 6*x = 1) ↔ (Real.cos 2*x - 1) * (2 * Real.cos 2*x + 1) * Real.cos 4*x = 0   :=  by sorry
