-- Prove2me | Theorems.Thm_lean_workbook_plus_19826
-- name    : lean_workbook_plus_19826
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/47eafde6-ce89-4fd0-bbed-6dbac4f236d1
-- statement:
--   $3^{2^n}-1=(3^{2^{n-1}}-1)(3^{2^{n-1}}+1)=(3^{2^{n-2}}-1)(3^{2^{n-2}}+1)(3^{2^{n-1}}+1)=\cdots = 2\prod_{k=0}^{n-1}(3^{2^k}+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19826 : ∀ n : ℕ, 3^(2^n) - 1 = 2 * ∏ k in Finset.range n, (3^(2^k) + 1)   :=  by sorry
