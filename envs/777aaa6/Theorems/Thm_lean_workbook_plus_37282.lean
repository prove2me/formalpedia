-- Prove2me | Theorems.Thm_lean_workbook_plus_37282
-- name    : lean_workbook_plus_37282
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/c8c4c153-04ec-4c5b-8704-0b8c66324512
-- statement:
--   Prove that $\binom{1}{1}+\binom{2}{1}+...+\binom{n}{1}=\binom{n+1}{2}=\frac{n(n+1)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37282 (n : ℕ) : ∑ k in Finset.Icc 1 n, (Nat.choose k 1) = Nat.choose (n + 1) 2   :=  by sorry
