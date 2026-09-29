-- Prove2me | Theorems.Thm_lean_workbook_plus_22436
-- name    : lean_workbook_plus_22436
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b5ec1b20-6552-4988-99a5-d12b9597dde7
-- statement:
--   Prove that if $a$ and $b$ are integers with $\gcd(a,b)=d$ , then there exist integers $x$ and $y$ such that $ax+by=d$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22436 (a b d : ℤ) (hd : d = gcd a b) : ∃ x y : ℤ, a * x + b * y = d   :=  by sorry
