-- Prove2me | Theorems.Thm_lean_workbook_plus_44527
-- name    : lean_workbook_plus_44527
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6b245da2-3f03-4b3e-8108-12cc84d77315
-- statement:
--   Prove that $ \displaystyle F_0 + F_1 + F_2 + \dots + F_N = F_{N+2} - 1$ , where $ F_N$ is the Nth Fibonacci number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44527 : ∀ n : ℕ, ∑ k in Finset.range (n+1), fib k = fib (n + 2) - 1   :=  by sorry
