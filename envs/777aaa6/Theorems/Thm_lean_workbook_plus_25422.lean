-- Prove2me | Theorems.Thm_lean_workbook_plus_25422
-- name    : lean_workbook_plus_25422
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/de0bdb09-5248-4143-8d10-d55d138f3b96
-- statement:
--   Prove that, for $n \in \mathbb{N}$ , \n\n $1 \times 2 + 2 \times 3 + 3 \times 4 + ... + n(n+1) = \frac{1}{3} n (n+1)(n+2)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25422 (n : ℕ) : ∑ k in Finset.range (n+1), k * (k+1) = (1/3 : ℚ) * n * (n+1) * (n+2)   :=  by sorry
