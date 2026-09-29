-- Prove2me | Theorems.Thm_lean_workbook_plus_18747
-- name    : lean_workbook_plus_18747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a48da7e9-b9c7-4eb7-b417-f2f5879b414b
-- statement:
--   Prove the final inequality using A.M.-G.M. inequality:\n$$\Big( \sum_{i=1}^{n}{t_ix_i}+ab\sum_{i=1}^{n}{\frac{t_i}{x_i}}\Big)^2 \geq 4ab\left(\sum_{i=1}^{n}{t_i x_i}\right)\left(\sum_{i=1}^{n}{\frac{t_i}{x_i}}\right)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18747 (n a b : ℕ) (t x : Fin n → ℝ) :
  (∑ i, t i * x i + a * b * ∑ i, t i / x i) ^ 2 ≥
  4 * a * b * (∑ i, t i * x i) * (∑ i, t i / x i)   :=  by sorry
