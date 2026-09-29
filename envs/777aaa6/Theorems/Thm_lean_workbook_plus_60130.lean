-- Prove2me | Theorems.Thm_lean_workbook_plus_60130
-- name    : lean_workbook_plus_60130
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/36b7dce3-8fa8-4db3-9fa7-75fb7b9adbfd
-- statement:
--   Prove that \n $$\\sum_{k=0}^n (-1)^k 2^{n-k} \\binom{n}{k}=1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60130 (n : ℕ) : ∑ k in Finset.range (n+1), (-1 : ℤ)^k * 2^(n-k) * (n.choose k) = 1   :=  by sorry
