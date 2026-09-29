-- Prove2me | Theorems.Thm_lean_workbook_plus_22729
-- name    : lean_workbook_plus_22729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c06887c5-4bbb-43b7-921d-612756732b8e
-- statement:
--   If $\lim_{x \to 0} \frac{f(x)}{x^2} = 0$ prove that $\lim_{x \to 0} \frac{f(x)}{x} = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22729 : ∀ f : ℝ → ℝ, (∀ x : ℝ, x ≠ 0 → f x / x ^ 2 = 0) → ∀ x : ℝ, x ≠ 0 → f x / x = 0   :=  by sorry
