-- Prove2me | Theorems.Thm_lean_workbook_plus_35816
-- name    : lean_workbook_plus_35816
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/12f30c6a-d12b-49c8-9526-e15c06bdfd87
-- statement:
--   Prove that, between positive integers $a$ and $b$ , $gcd(a,b)=1$ ; that is, $a$ and $b$ are relatively prime, if and only if there exist integers $x$ and $y$ such that $ax+by=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35816 (a b : ℤ) : gcd a b = 1 ↔ ∃ x y : ℤ, a * x + b * y = 1   :=  by sorry
