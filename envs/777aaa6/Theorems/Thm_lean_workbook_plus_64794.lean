-- Prove2me | Theorems.Thm_lean_workbook_plus_64794
-- name    : lean_workbook_plus_64794
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/29d2cfc3-00b2-4f4c-b464-9697c76b3948
-- statement:
--   Prove that $1+2+\dots+k+(k+1)=\frac{k(k+1)}{2}+(k+1)=\frac{k(k+1)}{2}+\frac{2(k+1)}{2}=\frac{(k+2)(k+1)}{2}=\frac{(k+1)((k+1)+1)}{2}$ for all integers $k\ge1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64794 : ∀ k : ℕ, (∑ i in Finset.range (k+1), i) = k * (k+1) / 2   :=  by sorry
