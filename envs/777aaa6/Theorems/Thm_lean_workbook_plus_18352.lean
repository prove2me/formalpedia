-- Prove2me | Theorems.Thm_lean_workbook_plus_18352
-- name    : lean_workbook_plus_18352
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ff0ea4d7-1da1-4495-9ae0-9b8be8f25954
-- statement:
--   Prove, that if $R_i \geq 1$, the following inequality holds:\n\n$ \sum^{n}_{i = 1}{\frac {{R}_{i}}{R_{i} + 1}}\leq\sqrt [n]{\prod^{n}_{i = 1}{R_{i}}}\cdot(\sum^{n}_{i=1}\frac{1}{R_{i}+1})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18352 (n : ℕ) (R : ℕ → ℕ) (hR : ∀ i, R i ≥ 1) :
  ∑ i in Finset.Icc 1 n, (R i / (R i + 1)) ≤
    (∏ i in Finset.Icc 1 n, R i)^(1/n) * (∑ i in Finset.Icc 1 n, (1 / (R i + 1)))   :=  by sorry
