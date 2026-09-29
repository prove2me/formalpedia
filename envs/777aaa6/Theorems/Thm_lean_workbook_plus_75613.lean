-- Prove2me | Theorems.Thm_lean_workbook_plus_75613
-- name    : lean_workbook_plus_75613
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a70c3724-6a17-4797-bf7b-338d8c9f7b33
-- statement:
--   A ten term arithmetic series adds to 80. If $a_3=7$ , what is $a_9$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75613 (a : ℕ → ℝ) (h : ∃ a0 d, ∀ n, a n = a0 + d * n) (h2 : ∑ i in Finset.range 10, a i = 80) (h3 : a 3 = 7) : a 9 = 9.4   :=  by sorry
