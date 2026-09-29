-- Prove2me | Theorems.Thm_lean_workbook_plus_55245
-- name    : lean_workbook_plus_55245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/bd764f66-fbc6-4275-b7cc-b0d8a698a3f6
-- statement:
--   Find $a_n$ for the sequence $(a_n)_{n\ge 1}$ defined by $a_1=0,a_2=1$ and $a_{n+2}=2a_{n+1}-2a_n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55245 (a : ℕ → ℤ) (a1 : a 0 = 0) (a2 : a 1 = 1) (a_rec : ∀ n, a (n + 2) = 2 * a (n + 1) - 2 * a n) : ∀ n, a (n + 2) = 2 * a (n + 1) - 2 * a n   :=  by sorry
