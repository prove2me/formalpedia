-- Prove2me | Theorems.Thm_lean_workbook_plus_61336
-- name    : lean_workbook_plus_61336
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/456429c7-f145-42a5-bb3b-1e21df7325d7
-- statement:
--   Prove the theorem: Let $a,b,c$ be three integer numbers so that $abc\ne 0$. Then the equation $ax+by=c$ has at least an integer solution if and only if the greatest common divisor of the numbers $a$ and $b$ divides the number $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61336 (a b c : ℤ) (habc : a * b * c ≠ 0) :  (∃ x y : ℤ, a * x + b * y = c) ↔ (gcd a b) ∣ c   :=  by sorry
