-- Prove2me | Theorems.Thm_lean_workbook_plus_73832
-- name    : lean_workbook_plus_73832
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/5e1a658f-62b8-4892-b8b0-07876771e02d
-- statement:
--   case1: $\sum_1^n b_i^2-(\sum_1^nb_i)^2)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73832 (n : ℕ) (b : ℕ → ℕ) : (∑ i in Finset.range n, (b i)^2) - (∑ i in Finset.range n, b i)^2 ≥ 0   :=  by sorry
