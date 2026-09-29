-- Prove2me | Theorems.Thm_lean_workbook_plus_19858
-- name    : lean_workbook_plus_19858
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a9c24ba1-6379-4abe-ac30-25408eaa3c65
-- statement:
--   Prove the following: $1+2+4+8...+2^n=2^{n+1}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19858 : ∀ n : ℕ, ∑ i in Finset.range (n+1), 2^i = 2^(n+1) - 1   :=  by sorry
