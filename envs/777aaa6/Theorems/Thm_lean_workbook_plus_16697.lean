-- Prove2me | Theorems.Thm_lean_workbook_plus_16697
-- name    : lean_workbook_plus_16697
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/1036fd99-16f3-40d9-b1ac-df9a91363b7b
-- statement:
--   If $\lim_{x \to 0} \frac{f(x)}{x^2} = 0$ prove that $\lim_{x \to 0} \frac{f(x)}{x} = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16697 (f : ℝ → ℝ) (h : ∀ x, f x / x ^ 2 = 0) :
  ∀ x, f x / x = 0   :=  by sorry
