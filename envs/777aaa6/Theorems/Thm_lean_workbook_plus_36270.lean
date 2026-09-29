-- Prove2me | Theorems.Thm_lean_workbook_plus_36270
-- name    : lean_workbook_plus_36270
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/90c3d7e7-8d4d-4e21-bd45-48a98a6d4f1e
-- statement:
--   Prove that if $a,n \in \mathbb N \wedge \gcd(a,n) = 1$ you can find $x, y \in \mathbb Z$ such that $ax + ny = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36270 {a n : ℕ} (h : Nat.gcd a n = 1) : ∃ x y : ℤ, a * x + n * y = 1   :=  by sorry
