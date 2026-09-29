-- Prove2me | Theorems.Thm_lean_workbook_plus_31037
-- name    : lean_workbook_plus_31037
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a4b15cec-c76b-442a-b373-833cb7873cbe
-- statement:
--   For $m=n=k$ , we have\n\n$\binom{2n}{n}=\sum_{k=0}^{n}\binom{n}{k}\binom{n}{n-k}\ =\sum_{k=0}^{n}\binom{n}{k}^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31037 : ∀ n : ℕ, (Nat.choose 2 * n) n = ∑ k in Finset.range (n+1), ((Nat.choose n k)^2)   :=  by sorry
