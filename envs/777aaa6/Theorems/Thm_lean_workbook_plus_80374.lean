-- Prove2me | Theorems.Thm_lean_workbook_plus_80374
-- name    : lean_workbook_plus_80374
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1ee743c6-f318-49fa-8f12-ecfdbe5da37c
-- statement:
--   Shoelace to yield $f(x) = x^2-1$ . Let $g(x) = \frac{1}{f(x)}$ . Then $g(x) = 0.5 \times \left( \frac{1}{x-1} - \frac{1}{x+1} \right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80374  (x : ℝ)
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 1)
  (h₁ : ∀ x, g x = 1 / f x)
  (h₂ : g x = 0.5 * (1 / (x - 1) - 1 / (x + 1))) :
  g x = 0.5 * (1 / (x - 1) - 1 / (x + 1))   :=  by sorry
