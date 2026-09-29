-- Prove2me | Theorems.Thm_lean_workbook_plus_11500
-- name    : lean_workbook_plus_11500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2c3877d0-5024-4d42-a904-8509842c3be3
-- statement:
--   Prove that $\gcd(n, n^2 + n + 1) = 1$ for all positive integers $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11500 (n : ℕ) : n.gcd (n^2 + n + 1) = 1   :=  by sorry
