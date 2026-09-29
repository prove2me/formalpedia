-- Prove2me | Theorems.Thm_lean_workbook_plus_60791
-- name    : lean_workbook_plus_60791
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b2daa3aa-5cbc-4624-92fe-b8551e7aa56f
-- statement:
--   Prove that $ \cos\theta + \sqrt{3}\sin\theta = 2\left(\frac{1}{2}\cos\theta + \frac{\sqrt{3}}{2}\sin\theta\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60791 (θ : ℝ) :
  Real.cos θ + Real.sqrt 3 * Real.sin θ =
    2 * (1 / 2 * Real.cos θ + Real.sqrt 3 / 2 * Real.sin θ)   :=  by sorry
