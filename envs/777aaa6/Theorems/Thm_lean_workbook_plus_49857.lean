-- Prove2me | Theorems.Thm_lean_workbook_plus_49857
-- name    : lean_workbook_plus_49857
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/9b669e81-830d-4275-9baf-3b7896d412ab
-- statement:
--   Because $ 2^{r}=(1+1)^{r}=\sum_{k=0}^{n}C_{r}^{k},\forall r \in \mathbb N$ our identity is equivalent to: $ \sum_{i=0}^{n}2^{k}\cdot C_{n}^{k}=(1+2)^{n}=3^{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49857 (n : ℕ) : ∑ k in Finset.range (n + 1), (2 : ℕ) ^ k * (n.choose k) = (3 : ℕ) ^ n   :=  by sorry
