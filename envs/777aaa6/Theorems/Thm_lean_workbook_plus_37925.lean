-- Prove2me | Theorems.Thm_lean_workbook_plus_37925
-- name    : lean_workbook_plus_37925
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4e116146-f230-4b57-a637-9387dc012fe3
-- statement:
--   Given the finite sequence\n\n$a_k= a_{k-1}+ \frac{a^2_{k-1}}{n}$ ; $k \in [1;n]$\n\nProve that\n\n$1- \frac{1}{n}<a_n<1$\n\n$a_0 = \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37925 (n : ℕ) (hn : 0 < n) (a : ℕ → ℝ) (ha : a 0 = 1/2) (ha' : ∀ k, a k = a (k - 1) + (a (k - 1))^2 / n) : 1 - 1 / n < a n ∧ a n < 1   :=  by sorry
