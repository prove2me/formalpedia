-- Prove2me | Theorems.Thm_lean_workbook_plus_7196
-- name    : lean_workbook_plus_7196
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ad2fd871-fb01-4173-afac-e6368ad0d3a3
-- statement:
--   Prove that $A(r,n)=\sum\limits_{i=0}^n (-1)^{i}{n\choose{i}}{(n-i)^{r}}$, where $A(r,n)$ denotes the number of ways that $r$ distinct balls are put into $n$ boxes such that there isn't any empty box.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7196 (r n : ℕ) (hn : 0 < n) : (∑ i in Finset.range (n + 1), (-1 : ℤ)^i * n.choose i * (n - i)^r) = (∑ i in Finset.range (n + 1), (-1 : ℤ)^i * n.choose i * (n - i)^r)   :=  by sorry
