-- Prove2me | Theorems.Thm_lean_workbook_plus_13490
-- name    : lean_workbook_plus_13490
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/899d31b1-e9a9-4d29-b136-81bd016e10f0
-- statement:
--   $ \sum_{k=1}^{n}2k+1=2\cdot\frac{n(n+1)}{2}+n=n(n+2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13490 : ∀ n, ∑ k in Finset.range n, (2 * k + 1) = n * (n + 2)   :=  by sorry
