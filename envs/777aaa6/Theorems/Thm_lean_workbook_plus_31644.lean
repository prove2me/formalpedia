-- Prove2me | Theorems.Thm_lean_workbook_plus_31644
-- name    : lean_workbook_plus_31644
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c59da304-be92-48d5-9172-ad8d266b3c2c
-- statement:
--   Prove that $ \cos\theta + \sqrt{3}\sin\theta = 2\left(\cos\theta\cos\frac{\pi}{3} + \sin\theta\sin\frac{\pi}{3}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31644 (θ : ℝ) :
  Real.cos θ + Real.sqrt 3 * Real.sin θ =
    2 * (Real.cos θ * Real.cos (Real.pi / 3) + Real.sin θ * Real.sin (Real.pi / 3))   :=  by sorry
