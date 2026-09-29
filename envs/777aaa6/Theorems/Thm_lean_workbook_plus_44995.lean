-- Prove2me | Theorems.Thm_lean_workbook_plus_44995
-- name    : lean_workbook_plus_44995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c28235c7-3b26-4002-a458-1fbf828e702d
-- statement:
--   If $n = 6k$ for some $k$ , $gcd(k, 6) = 1$ , $k > 1$ , then $n < f(n)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44995 (n : ℕ) (k : ℕ) (h₁ : n = 6 * k) (h₂ : Nat.gcd k 6 = 1) (h₃ : k > 1) : n < Nat.factorial n   :=  by sorry
