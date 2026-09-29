-- Prove2me | Theorems.Thm_lean_workbook_plus_55459
-- name    : lean_workbook_plus_55459
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/9c4e4197-8ec7-4bcb-8049-d28b778443b5
-- statement:
--   Given that $n$ is relatively prime to $2n+1$, prove that $\gcd(n,2n+1) = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55459 (n : ℕ) : Nat.Coprime n (2 * n + 1) ↔ Nat.gcd n (2 * n + 1) = 1   :=  by sorry
