-- Prove2me | Theorems.Thm_lean_workbook_plus_67574
-- name    : lean_workbook_plus_67574
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/af22c16a-ae72-4706-97ec-71313c9b25ae
-- statement:
--   We want to note that $b_k\ge0$ for all $k$ and that $\sum_{k=0}^nb_k=1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67574  (n : ℕ)
  (b : ℕ → NNReal)
  (h₀ : ∑ k in Finset.range (n + 1), b k = 1) :
  ∀ k, 0 ≤ b k   :=  by sorry
