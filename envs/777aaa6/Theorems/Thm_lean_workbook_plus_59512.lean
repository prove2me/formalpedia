-- Prove2me | Theorems.Thm_lean_workbook_plus_59512
-- name    : lean_workbook_plus_59512
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b9cd636f-a0cb-4403-909c-82a8e9e13e56
-- statement:
--   Prove that $ \frac{\cos\theta + \sqrt{3}\sin\theta}{2} = \cos\left(\theta-\frac{\pi}{3}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59512 : ∀ θ : ℝ, (cos θ + Real.sqrt 3 * sin θ) / 2 = cos (θ - Real.pi / 3)   :=  by sorry
