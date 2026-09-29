-- Prove2me | Theorems.Thm_lean_workbook_plus_70339
-- name    : lean_workbook_plus_70339
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3008e230-0892-4686-8c85-cb77740842cd
-- statement:
--   Prove that $\sum\limits_{k=1}^{n}{{\frac{k}{2^k+k}}}< \frac{3}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70339 : ∀ n : ℕ, ∑ k in Finset.Icc 1 n, (k / (2 ^ k + k)) < 3 / 2   :=  by sorry
