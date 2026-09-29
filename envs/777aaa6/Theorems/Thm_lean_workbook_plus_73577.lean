-- Prove2me | Theorems.Thm_lean_workbook_plus_73577
-- name    : lean_workbook_plus_73577
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e6b5f295-c952-4030-a564-707f8c8f5d36
-- statement:
--   (x+y)^k=\sum^{k}_{r=0} {\binom{k}{r} x^{k-r}y^r}........there are $2^{k}$ terms in form of $x^{k-r}y^r$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73577 (x y : ℝ) (k : ℕ) : (x + y) ^ k = ∑ r in Finset.range (k + 1), (k.choose r) * x ^ (k - r) * y ^ r   :=  by sorry
