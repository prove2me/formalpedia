-- Prove2me | Theorems.Thm_lean_workbook_plus_80677
-- name    : lean_workbook_plus_80677
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2a0c5d0e-ef96-4e6f-82cc-587989313e8f
-- statement:
--   $\binom{2n+1}{0}+\binom{2n+1}{1}+\binom{2n+1}{2}+...+\binom{2n+1}{2n+1}= 2^{2n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80677 (n : ℕ) : ∑ k in Finset.range (2*n+2), choose (2*n+1) k = 2^(2*n+1)   :=  by sorry
