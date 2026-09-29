-- Prove2me | Theorems.Thm_lean_workbook_plus_66744
-- name    : lean_workbook_plus_66744
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/75b22fa1-b831-4003-a43c-f2c194a8fc79
-- statement:
--   Prove that if $b_i > 0$ for all $i$, then $\prod_{i=1}^j b_j > 0$ for all $j$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66744 (b : ℕ → ℕ) (h : ∀ i, b i > 0) : ∀ j, ∏ i in Finset.range j, b i > 0   :=  by sorry
