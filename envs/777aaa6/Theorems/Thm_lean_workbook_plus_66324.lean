-- Prove2me | Theorems.Thm_lean_workbook_plus_66324
-- name    : lean_workbook_plus_66324
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/24f60e31-d45c-4205-9830-fe83a090e466
-- statement:
--   Prove that\n $ \dfrac{1}{2} + \dfrac{1}{3} + ... + \dfrac{1}{2^{2n}} > n,\nfor all positive integers $ n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66324 : ∀ n : ℕ, (∑ k in Finset.Icc 1 n, (1 : ℝ) / (2 ^ k)) > n   :=  by sorry
