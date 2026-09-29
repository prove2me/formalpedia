-- Prove2me | Theorems.Thm_lean_workbook_plus_13430
-- name    : lean_workbook_plus_13430
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4d44343c-6a96-4013-aa8a-592cc2559347
-- statement:
--   Prove that $\sum_{i=0}^n \binom{n}{i} = 2^n$ for all $n \in \mathbb{Z}^+$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13430 (n : ℕ) : ∑ i in Finset.range (n+1), choose n i = 2 ^ n   :=  by sorry
