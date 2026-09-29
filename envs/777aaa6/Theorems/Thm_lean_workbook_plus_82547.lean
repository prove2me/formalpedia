-- Prove2me | Theorems.Thm_lean_workbook_plus_82547
-- name    : lean_workbook_plus_82547
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2732b32a-7fb1-4839-9c06-1c4d511c2ba6
-- statement:
--   Find the moment generating function of a random variable X that has the Poisson distribution $ p(x ; \mu) = \frac {e^{-\mu} \mu^{x}}{x!} $ for $ x = 0,1,2,... $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82547 (X : ℕ → ℝ) (μ : ℝ) (p : ℕ → ℝ) (hp : ∀ x, p x = (Real.exp (-μ) * μ ^ x)/x!) : ∃ M : ℝ → ℝ, ∀ t, M t = ∑' x : ℕ, (p x) * (Real.exp (t * x))   :=  by sorry
