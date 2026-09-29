-- Prove2me | Theorems.Thm_lean_workbook_plus_56140
-- name    : lean_workbook_plus_56140
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/1c1d980e-94a9-4de6-a36c-d4cc5888bfea
-- statement:
--   Prove that:\n\n$ (1+\cos\theta)(1+\cos\alpha) = 4\cos^{2}\frac{\theta}{2}\cos^{2}\frac{\alpha}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56140 (α θ : ℝ) : (1 + Real.cos θ) * (1 + Real.cos α) = 4 * (Real.cos (θ / 2))^2 * (Real.cos (α / 2))^2   :=  by sorry
