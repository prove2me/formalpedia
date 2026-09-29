-- Prove2me | Theorems.Thm_lean_workbook_plus_6726
-- name    : lean_workbook_plus_6726
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c5439361-dec1-47b0-b298-b57aed3671fc
-- statement:
--   Prove that: $ \sum_{k=1}^{n} (-1)^{k}{ \cdot } [ \log_{2}k ]=\frac{1+(-1)^n}{2}{ \cdot }[ \log_{2}n ]$ , where $[ . ]$ denote the integer part
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6726 : ∀ n : ℕ, ∑ k in Finset.range n, (-1 : ℤ)^k * Int.floor (Real.logb 2 k) = (1 + (-1)^n)/2 * Int.floor (Real.logb 2 n)   :=  by sorry
