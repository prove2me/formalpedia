-- Prove2me | Theorems.Thm_lean_workbook_plus_69076
-- name    : lean_workbook_plus_69076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/60954da7-ea84-4226-9fa0-1656edc7fb83
-- statement:
--   Let $a$ and $b$ be positive integers. Prove that there exist positive integers $x$ and $y$ such that: $ \binom{x+y}{2} = ax + by $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69076 (a b : ℕ) (hab : 0 < a ∧ 0 < b) : ∃ x y : ℕ, (Nat.choose (x+y) 2 = a*x + b*y)   :=  by sorry
