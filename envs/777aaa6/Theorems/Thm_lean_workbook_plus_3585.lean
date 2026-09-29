-- Prove2me | Theorems.Thm_lean_workbook_plus_3585
-- name    : lean_workbook_plus_3585
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/597957d9-67d9-4227-93ce-748da9322c7c
-- statement:
--   Given $a_{1}=3$ and $2a_{n+1}=(a_{n})^2+1$, prove that $\sum_{k=1}^{n} \frac {1}{a_{k}+1} <\frac {1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3585 (n : ℕ) (a : ℕ → ℕ) (ha : a 1 = 3) (hab : ∀ k, a (k + 1) = (a k)^2 + 1) : ∑ k in Finset.Icc 1 n, (1 / (a k + 1)) < 1 / 2   :=  by sorry
