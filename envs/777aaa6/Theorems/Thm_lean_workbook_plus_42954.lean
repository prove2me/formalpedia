-- Prove2me | Theorems.Thm_lean_workbook_plus_42954
-- name    : lean_workbook_plus_42954
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/8a01bb5f-e092-44cd-a1d3-ebcbd5cd8680
-- statement:
--   Therefore the total number is $\sum_{k=1}^5 \binom {5} {k} k^{5-k} = 5\cdot 1^4 + 10\cdot 2^3 + 10\cdot 3^2 + 5\cdot 4^1 + 1\cdot 5^0 = 196$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42954 ∑ k in Finset.Icc 1 5, (Nat.choose 5 k) * k^(5-k) = 196   :=  by sorry
