-- Prove2me | Theorems.Thm_lean_workbook_plus_19821
-- name    : lean_workbook_plus_19821
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7daef86c-1b21-41bc-ab6e-f977398e7c68
-- statement:
--   Prove that $f(\xi,t)=e^{-\frac{\xi^{2}}{4t}}$ is uniformly convergent using the Weierstrass M-Test. Given that there exists a constant $t_{0}>0$ such that $t \ge t_{0}$ for all $t$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19821 (f : ℝ → ℝ → ℝ) (t₀ : ℝ) (ht : ∀ t, t₀ ≤ t) (ξ : ℝ) : UniformContinuousOn (fun t : ℝ => exp (-ξ^2 / (4 * t))) (Set.Ici t₀)   :=  by sorry
