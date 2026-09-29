-- Prove2me | Theorems.Thm_lean_workbook_plus_1762
-- name    : lean_workbook_plus_1762
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f86691b8-f8c9-4a63-9215-9a1e300ac47a
-- statement:
--   $ \sum_{k = 2}^{n}{\frac {1}{k^2}} < \sum_{k = 2}^{n}{(\frac {1}{k - 1} - \frac {1}{k})} = \frac {n - 1}{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1762 (n : ℕ) (hn : 2 ≤ n) : ∑ k in Finset.Icc 2 n, (1 / (k - 1) - 1 / k) = (n - 1) / n ∧ ∑ k in Finset.Icc 2 n, 1 / k ^ 2 < ∑ k in Finset.Icc 2 n, (1 / (k - 1) - 1 / k)   :=  by sorry
