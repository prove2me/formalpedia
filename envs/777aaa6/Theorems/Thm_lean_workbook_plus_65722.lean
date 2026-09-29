-- Prove2me | Theorems.Thm_lean_workbook_plus_65722
-- name    : lean_workbook_plus_65722
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/915d10f3-40e7-48b0-94b0-188e36fd723c
-- statement:
--   Express the limit as a Riemann sum and evaluate: $\lim_{n\to \infty}{\frac{n}{\sqrt[n]{n!}}} = \lim_{n\to\infty} \frac{1}{n}\sum_{k=1}^{n}ln(\frac{n}{k})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65722 : ∀ n : ℕ, ((n:ℝ) / (n! :ℝ) ^ (1/n)) = (1/n) * ∑ k in Finset.range n, Real.log (n/k)   :=  by sorry
