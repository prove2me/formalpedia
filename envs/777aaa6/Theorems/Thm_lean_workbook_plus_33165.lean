-- Prove2me | Theorems.Thm_lean_workbook_plus_33165
-- name    : lean_workbook_plus_33165
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/0fee3444-d4d4-41fb-bd8e-426be962d6ba
-- statement:
--   Prove that $2k \equiv n \mod 2k-n$ for all even numbers $k$ and $n$ such that $n \leq k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33165 (k n : ℕ) (h₁ : Even k) (h₂ : Even n) (h₃ : n ≤ k) : 2 * k ≡ n [ZMOD 2 * k - n]   :=  by sorry
