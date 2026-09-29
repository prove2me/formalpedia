-- Prove2me | Theorems.Thm_lean_workbook_plus_78116
-- name    : lean_workbook_plus_78116
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/abb9367e-d47b-4d03-9237-eb006662a3d9
-- statement:
--   Prove that for positive numbers $a_1, a_2, ..., a_n$ and $b_1 \leq b_2 \leq ... \leq b_n$ such that $a_1 \leq b_1$, $a_1 + a_2 \leq b_1 + b_2$, ..., $a_1 + a_2 + ... + a_n \leq b_1 + b_2 + ... + b_n$, the following inequality holds: $\sqrt{a_1} + \sqrt{a_2} + ... + \sqrt{a_n} \leq \sqrt{b_1} + \sqrt{b_2} + ... + \sqrt{b_n}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78116 (n : ℕ) (a b : ℕ → ℝ) (hb : Monotone b) (hab : ∀ i, 0 ≤ a i) (h : ∀ i, a i ≤ b i) (h' : ∀ i, ∑ j in Finset.range (i + 1), a j ≤ ∑ j in Finset.range (i + 1), b j) : ∑ i in Finset.range n, Real.sqrt (a i) ≤ ∑ i in Finset.range n, Real.sqrt (b i)   :=  by sorry
