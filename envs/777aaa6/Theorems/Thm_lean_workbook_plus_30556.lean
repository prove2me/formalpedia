-- Prove2me | Theorems.Thm_lean_workbook_plus_30556
-- name    : lean_workbook_plus_30556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ff896967-e115-4e39-ae3e-4bb0a122d31c
-- statement:
--   Find the smallest positive integer m such that $k^m \equiv 1 \pmod{4p+1}$ given $k^4 \equiv 1 \pmod{4p+1}$ and $k < 4p+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30556 (p : ℕ) (k : ℕ) (h₁ : k < 4 * p + 1) (h₂ : k ^ 4 ≡ 1 [ZMOD 4 * p + 1]) : ∃ m : ℕ, k ^ m ≡ 1 [ZMOD 4 * p + 1] ∧ m < 4 * p + 1   :=  by sorry
