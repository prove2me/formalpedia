-- Prove2me | Theorems.Thm_lean_workbook_plus_43262
-- name    : lean_workbook_plus_43262
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/517a4b96-a9d0-40a7-9c19-1dcfa1f40463
-- statement:
--   $ \sum_{n = 1}^{98} n(100 - n) = \sum_{n = 1}^{98} (100n - n^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43262 (n : ℕ) : ∑ n in Finset.Icc 1 98, n * (100 - n) = ∑ n in Finset.Icc 1 98, (100 * n - n ^ 2)   :=  by sorry
