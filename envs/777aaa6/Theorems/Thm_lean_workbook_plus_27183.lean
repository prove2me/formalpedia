-- Prove2me | Theorems.Thm_lean_workbook_plus_27183
-- name    : lean_workbook_plus_27183
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b18cf5ca-3a04-4e96-b26f-c813d6773b77
-- statement:
--   Prove the formula: $\frac{1}{1\times2}+\frac{1}{2\times3}+\frac{1}{3\times4}+....+\frac{1}{n(n+1)}=\frac{n}{n+1}$ using mathematical induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27183 : ∀ n : ℕ, (∑ k in Finset.range n, (1 : ℝ) / (k * (k + 1))) = n / (n + 1)   :=  by sorry
