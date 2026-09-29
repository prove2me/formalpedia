-- Prove2me | Theorems.Thm_lean_workbook_plus_60790
-- name    : lean_workbook_plus_60790
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/1493f3a1-a380-4412-985a-a6ad6a57f34c
-- statement:
--   Prove the identity $\cos^4\theta = \frac{1}{2}\cos2\theta + \frac{1}{8}\cos4\theta + \frac{3}{8}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60790 : ∀ θ : ℝ, (cos θ)^4 = (1 / 2) * cos (2 * θ) + (1 / 8) * cos (4 * θ) + 3 / 8   :=  by sorry
