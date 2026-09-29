-- Prove2me | Theorems.Thm_lean_workbook_plus_25911
-- name    : lean_workbook_plus_25911
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8ef1ff7f-c87c-495a-9472-4e3a8c0b106a
-- statement:
--   Prove Pascal's Identity: $ \binom{n}{k}=\binom{n-1}{k-1}+\binom{n-1}{k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25911 {n k : ℕ} (h₁ : 1 ≤ k) (h₂ : k ≤ n) : choose n k = choose (n - 1) (k - 1) + choose (n - 1) k   :=  by sorry
