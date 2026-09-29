-- Prove2me | Theorems.Thm_lean_workbook_plus_57272
-- name    : lean_workbook_plus_57272
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fecdf31a-5aba-45e2-92b9-21b80e0837b0
-- statement:
--   $\sum_{k=1}^{n-2}\frac{k(k+1)}{n+k} < \sum_{k=1}^{n-2}\frac{k}{2}=\frac{(n-1)(n-2)}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57272 : ∀ n, n ≥ 4 → ∑ k in Finset.Ico 1 (n - 2), (k * (k + 1) / (k + n)) < ∑ k in Finset.Ico 1 (n - 2), (k / 2)   :=  by sorry
