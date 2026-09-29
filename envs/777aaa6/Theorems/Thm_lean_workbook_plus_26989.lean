-- Prove2me | Theorems.Thm_lean_workbook_plus_26989
-- name    : lean_workbook_plus_26989
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/2aee1197-9190-43f3-92c2-6cc33c4503c7
-- statement:
--   Prove that $n^2-1$ is divisible by $8$ if $n$ is an odd positive integer using the identity $n=2m+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26989 {n : ℕ} (h : n = 2*m + 1) : 8 ∣ n^2 - 1   :=  by sorry
