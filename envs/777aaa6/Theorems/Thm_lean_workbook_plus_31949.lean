-- Prove2me | Theorems.Thm_lean_workbook_plus_31949
-- name    : lean_workbook_plus_31949
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/046bcf0d-5571-418c-a012-0df6164e5558
-- statement:
--   Prove that $\sum^{n}_{k=0}{2n+1\choose 2k+1}2^{k}$ is equal to $\frac{1}{2}(9^{2n+1}-7^{2n+1})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31949 (n : ℕ) : ∑ k in Finset.range (n+1), (Nat.choose (2*n+1) (2*k+1)) * (2^k) = (1/2) * (9^(2*n+1) - 7^(2*n+1))   :=  by sorry
