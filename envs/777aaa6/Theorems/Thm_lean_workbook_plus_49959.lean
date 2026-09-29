-- Prove2me | Theorems.Thm_lean_workbook_plus_49959
-- name    : lean_workbook_plus_49959
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e0401531-9661-4580-8c21-7509c16a2804
-- statement:
--   Prove the following using induction $\binom{n}{k-1}+\binom{n}{k}= \binom{n+1}{k}$\n$0 < k \le n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49959 (n k : ℕ) (h₁ : 0 < k) (h₂ : k ≤ n) : choose n (k - 1) + choose n k = choose (n + 1) k   :=  by sorry
