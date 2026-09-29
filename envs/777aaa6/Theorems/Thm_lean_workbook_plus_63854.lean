-- Prove2me | Theorems.Thm_lean_workbook_plus_63854
-- name    : lean_workbook_plus_63854
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9cb2907e-bdba-4b39-bf3f-90f7047ebfba
-- statement:
--   Prove that $ \cos\theta + \sqrt{3}\sin\theta = 2\left(\frac{1}{2}\cos\theta+\frac{\sqrt{3}}{2}\sin\theta\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63854 (θ : ℝ) : cos θ + Real.sqrt 3 * sin θ = 2 * (1 / 2 * cos θ + Real.sqrt 3 / 2 * sin θ)   :=  by sorry
