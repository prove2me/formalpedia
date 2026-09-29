-- Prove2me | Theorems.Thm_lean_workbook_plus_16568
-- name    : lean_workbook_plus_16568
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/955b12a4-c5d5-4f03-b1df-626aad7f1b23
-- statement:
--   In polar coordinates: $ x^2 + y^2 - 2x\ge0$ becomes $ r^2 - 2r\cos\theta\ge0.$ Adopt the convention that $ r\ge 0$ always (which is the most useful convention for integration, since you don't want to double-count) and this become $ r\ge2\cos\theta.$ (Really, $ r\ge\max(2\cos\theta,0).$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16568 : ∀ r θ : ℝ, r >= 0 → r >= 2 * Real.cos θ   :=  by sorry
