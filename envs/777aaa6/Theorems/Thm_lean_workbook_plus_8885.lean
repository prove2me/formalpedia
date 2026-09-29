-- Prove2me | Theorems.Thm_lean_workbook_plus_8885
-- name    : lean_workbook_plus_8885
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/08638228-ec37-4515-b50f-03cf427baa14
-- statement:
--   Let $P_n(x)=\prod_{k=0}^n(x^{2^k}-1)$\nIt is easy to prove with induction that :\n\* all coefficients of $P_n$ are in $\{-1,0,1\}$\n\* $(x-1)^n|P_n(x)$\n\* two highest degree summands of $P_n(x)$ are $x^{2^{n+1}-1}-x^{2^{n+1}-2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8885 (n : ℕ) : (x - 1) ^ n ∣ ∏ k in Finset.range (n + 1), (x ^ (2 ^ k) - 1)   :=  by sorry
