-- Prove2me | Theorems.Thm_lean_workbook_plus_72732
-- name    : lean_workbook_plus_72732
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2c1c40da-1aec-41c5-9b0a-e14c51307d62
-- statement:
--   Generalizing: $x^n+y^n \leq 2^n+3^n$ \n\n $n \in N$ and $n \geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72732 (n : ℕ) (hn : 1 ≤ n) : ∀ x y : ℕ, x^n+y^n ≤ 2^n+3^n   :=  by sorry
