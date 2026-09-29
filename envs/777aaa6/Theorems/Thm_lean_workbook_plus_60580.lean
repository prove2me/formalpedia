-- Prove2me | Theorems.Thm_lean_workbook_plus_60580
-- name    : lean_workbook_plus_60580
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2b31d677-ba85-4b6a-a93c-55ec942d618c
-- statement:
--   Let $n,k$ be given positive integers with $n>k$ . Prove that: \n $ \frac{1}{n+1} \cdot \frac{n^n}{k^k (n-k)^{n-k}} < \frac{n!}{k! (n-k)!} < \frac{n^n}{k^k(n-k)^{n-k}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60580 : ∀ n k : ℕ, n > k → (1 / (n + 1) * n ^ n / (k ^ k * (n - k) ^ (n - k))) < n! / (k! * (n - k)!) ∧ n! / (k! * (n - k)!) < n ^ n / (k ^ k * (n - k) ^ (n - k))   :=  by sorry
