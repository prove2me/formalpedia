-- Prove2me | Theorems.Thm_lean_workbook_plus_15037
-- name    : lean_workbook_plus_15037
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b127c107-ad9b-44b7-98f8-30329552596f
-- statement:
--   The sets of all common divisors of $a+m\cdot b,\; b$ and $a,\; b$ are the same: $d\mid a,b\implies d\mid a+m\cdot b$ and $d\mid b,\; a+m\cdot b\implies d\mid a+m\cdot b-m\cdot b= a$ , so their maximums $\gcd(a+m\cdot b,\; b)$ and $\gcd(a,\; b)$ are equal.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15037  (a b m : ℕ) :
  Nat.gcd (a + m * b) b = Nat.gcd a b   :=  by sorry
