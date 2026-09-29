-- Prove2me | Theorems.Thm_lean_workbook_plus_23347
-- name    : lean_workbook_plus_23347
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/400ac837-12b3-44d1-ad02-95c0d55cc88a
-- statement:
--   Find the least common multiple (lcm) of two numbers $a$ and $b$ given that their greatest common divisor (gcd) is 13 and their product is 897.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23347 (a b : ℕ) (h1 : Nat.gcd a b = 13) (h2 : a * b = 897) : Nat.lcm a b = 69   :=  by sorry
