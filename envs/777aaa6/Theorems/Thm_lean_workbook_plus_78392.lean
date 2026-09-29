-- Prove2me | Theorems.Thm_lean_workbook_plus_78392
-- name    : lean_workbook_plus_78392
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8a9c29f5-cd45-4b97-b6e8-41f63d3feb7a
-- statement:
--   Prove that $\sin{x}-\cos{x}=-\sqrt{2}\sin{(x-\frac{\pi}{4})}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78392 : ∀ x : ℝ, sin x - cos x = -Real.sqrt 2 * sin (x - π / 4)   :=  by sorry
