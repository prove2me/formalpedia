-- Prove2me | Theorems.Thm_lean_workbook_plus_18336
-- name    : lean_workbook_plus_18336
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/34e5397f-600d-4f48-9f4c-dffd7edaf28a
-- statement:
--   Prove that $\sum (a-1)^{2}+\frac{\sum (a-b)^{2}}{2}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18336 (n : ℕ) (a : ℕ → ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (a i - 1) ^ 2) + (1 / 2) * (∑ i in Finset.range n, (a i - b i) ^ 2) ≥ 0   :=  by sorry
