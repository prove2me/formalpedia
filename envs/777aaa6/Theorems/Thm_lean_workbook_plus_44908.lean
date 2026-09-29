-- Prove2me | Theorems.Thm_lean_workbook_plus_44908
-- name    : lean_workbook_plus_44908
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6718769c-9393-4e91-a6db-9d5749cd6c34
-- statement:
--   Given fixed $a>0,f:\mathbb{R}_{0}^{+} \rightarrow \mathbb{R}$, $f(a)=1$ and $f(x)f(y)+f(\frac{a}{x})f(\frac{a}{y})=2f(xy)$ for all positive reals. Prove that $f(x)$ is constant.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44908 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) (hf : ∀ x y : ℝ, (x * y > 0 ∧ f x * f y + f (a / x) * f (a / y) = 2 * f (x * y))) : ∃ c :ℝ, ∀ x : ℝ, (x > 0 → f x = c)   :=  by sorry
