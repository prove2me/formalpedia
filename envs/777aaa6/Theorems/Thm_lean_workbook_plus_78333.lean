-- Prove2me | Theorems.Thm_lean_workbook_plus_78333
-- name    : lean_workbook_plus_78333
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/738decfb-7be2-4891-a5ba-f51b1225f8ad
-- statement:
--   Show that for $\theta_n \in (0, \frac{\pi}{2})$, there exists a unique solution $\theta_{n+1} = \frac{1}{3}(\theta_{n} + \pi)$ on $(0, \frac{\pi}{2})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78333 (n : ℕ) (θ_n : ℝ) (h₁ : 0 < θ_n ∧ θ_n < π/2) : ∃! θ_n1 : ℝ, θ_n1 = (θ_n + π)/3 ∧ 0 < θ_n1 ∧ θ_n1 < π/2   :=  by sorry
