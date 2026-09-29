-- Prove2me | Theorems.Thm_lean_workbook_plus_65202
-- name    : lean_workbook_plus_65202
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e32f290a-0abc-41e8-85ee-a5a9594766d8
-- statement:
--   If n is a positive integer，prove that $0< \sum_{k=0}^{n} \frac{\left ( -1 \right )^{k}C_{n}^{k}}{\sqrt{1+k}} < 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65202 : ∀ n : ℕ, 0 < ∑ k in Finset.range (n + 1), ((-1:ℝ)^(k) * (n.choose k) / (Real.sqrt (1 + k))) ∧ ∑ k in Finset.range (n + 1), ((-1:ℝ)^(k) * (n.choose k) / (Real.sqrt (1 + k))) < 1   :=  by sorry
