-- Prove2me | Theorems.Thm_lean_workbook_plus_51362
-- name    : lean_workbook_plus_51362
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b1cb60a3-605a-4e96-90ca-d1f14c3b9117
-- statement:
--   All primes of the form $4k-1$, where $p>5$, hold the property that $\frac{p+1}{2}$ must be even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51362 (p : ℕ) (h₁ : Nat.Prime p) (h₂ : p > 5) (h₃ : p = 4 * k - 1) : (p + 1) / 2 = 2 * k   :=  by sorry
