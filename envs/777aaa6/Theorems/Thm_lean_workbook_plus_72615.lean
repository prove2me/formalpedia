-- Prove2me | Theorems.Thm_lean_workbook_plus_72615
-- name    : lean_workbook_plus_72615
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c3b5d25b-4743-40e9-ab2a-5104552829aa
-- statement:
--   Give a combinatorial proof that $\binom{0}{k}+\binom{1}{k}+\binom{2}{k}+...\binom{n}{k}=\binom{n+1}{k+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72615 (n k : ℕ) (h₁ : n = 0) (h₂ : k ≤ n) : ∑ i in Finset.range (n + 1), choose i k = choose (n + 1) (k + 1)   :=  by sorry
