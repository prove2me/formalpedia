-- Prove2me | Theorems.Thm_lean_workbook_plus_66512
-- name    : lean_workbook_plus_66512
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e5ab3485-05af-4526-ad00-6a9dd2f197ca
-- statement:
--   Prove that $k(2n+1-k) \leq n(n+1)$ for all $1\leq k \leq 2n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66512 (n k : ℕ) (h₁ : 1 ≤ k) (h₂ : k ≤ 2 * n) : k * (2 * n + 1 - k) ≤ n * (n + 1)   :=  by sorry
