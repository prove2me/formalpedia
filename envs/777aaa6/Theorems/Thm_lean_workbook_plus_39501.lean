-- Prove2me | Theorems.Thm_lean_workbook_plus_39501
-- name    : lean_workbook_plus_39501
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/7b7d9270-3f08-4e64-bf54-85615acfc0f6
-- statement:
--   Check that $\sum_{k=1}^n \frac {1} {k^2} < \frac {5} {3}$ , for $n=1,2,3,4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39501 : ∀ n : ℕ, n ∈ ({1, 2, 3, 4} : Finset ℕ) → ∑ k in Finset.Icc 1 n, (1 : ℝ) / k ^ 2 < 5 / 3   :=  by sorry
