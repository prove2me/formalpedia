-- Prove2me | Theorems.Thm_lean_workbook_plus_51135
-- name    : lean_workbook_plus_51135
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b4396f59-19bb-4209-bb2d-7035070244c1
-- statement:
--   $\sum_{k=1}^n n(n+1)=\frac{n(n+1)(2n+1)}{6}+\frac{n(n+1)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51135 : ∀ n, ∑ k in Finset.range n, k * (k + 1) = n * (n + 1) * (2 * n + 1) / 6 + n * (n + 1) / 2   :=  by sorry
