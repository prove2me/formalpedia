-- Prove2me | Theorems.Thm_lean_workbook_plus_56239
-- name    : lean_workbook_plus_56239
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/81557f6e-2545-4fff-9127-f63fbe70ba67
-- statement:
--   If in the sequence $a_1, a_2, \cdots $ every integer number, $n$ , appears at least once, then exist to index $i$ such that $a_i = n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56239 (n : ℤ) (a : ℕ → ℤ) (h : ∀ n, ∃ i, a i = n) : ∃ i, a i = n   :=  by sorry
