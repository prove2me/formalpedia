-- Prove2me | Theorems.Thm_lean_workbook_plus_49745
-- name    : lean_workbook_plus_49745
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/02b11e41-8266-480b-9118-f643927196b7
-- statement:
--   Prove the linear representation of the greatest common divisor (gcd) of two integers $a$ and $b$, i.e., that there exist integers $x$ and $y$ such that $\text{gcd}(a, b) = xa + yb$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49745 (a b : ℤ) : ∃ x y : ℤ, gcd a b = x * a + y * b   :=  by sorry
