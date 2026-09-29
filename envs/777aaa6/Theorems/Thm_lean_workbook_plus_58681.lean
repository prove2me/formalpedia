-- Prove2me | Theorems.Thm_lean_workbook_plus_58681
-- name    : lean_workbook_plus_58681
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/28f33d1d-4f0d-4e2f-8fd1-5926a6cb562d
-- statement:
--   Prove that $\sum_{i=1}^{n} \frac{1}{i^2} \le 2 \sum_{i=1}^{n} \frac{1}{i(i+1)} = 2\sum_{i=1}^{n} \frac{1}{i} - \frac{1}{i+1} = 2 - \frac{2}{n+1} < 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58681 : ∀ n : ℕ, (∑ i in Finset.Icc 1 n, (1 / i ^ 2)) ≤ 2 * (∑ i in Finset.Icc 1 n, (1 / (i * (i + 1))))   :=  by sorry
