-- Prove2me | Theorems.Thm_lean_workbook_plus_73284
-- name    : lean_workbook_plus_73284
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/fae3504e-781a-485f-9011-5a1e4a34ddfd
-- statement:
--   Derive the formula for the sum of the first n squares: $ \sum_{k=1}^{n}k^{2}= \frac{n(n+1)(2n+1)}{6}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73284 : ∀ n, ∑ k in Finset.range n, k^2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry
