-- Prove2me | Theorems.Thm_lean_workbook_plus_66388
-- name    : lean_workbook_plus_66388
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/ef1bac53-9218-4d22-bc9c-c4baf3e7bedb
-- statement:
--   Prove that $lcm(a,b)=\frac{a.b}{gcd(a,b)}$ using the properties of $gcd$ and $lcm$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66388 (a b : ℕ) : Nat.lcm a b = a * b / Nat.gcd a b   :=  by sorry
