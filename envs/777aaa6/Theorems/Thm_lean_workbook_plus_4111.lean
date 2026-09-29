-- Prove2me | Theorems.Thm_lean_workbook_plus_4111
-- name    : lean_workbook_plus_4111
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/082c4082-f85b-4919-b977-237f273f769a
-- statement:
--   Solve for $x$: \n $ \frac{1}{\sqrt{3}}\sin x(\sin x-\cos x)+\cos x(\sin x-\cos x)\geq 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4111 : ∀ x : ℝ, (1 / Real.sqrt 3) * Real.sin x * (Real.sin x - Real.cos x) + Real.cos x * (Real.sin x - Real.cos x) ≥ 0   :=  by sorry
