-- Prove2me | Theorems.Thm_lean_workbook_plus_16464
-- name    : lean_workbook_plus_16464
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d091289c-7d97-4d59-87c3-b7ac000ca862
-- statement:
--   Prove that if $d = gcd(a, b)$, then there exist integers $x$ and $y$ such that $d = ax+by$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16464 (a b d : ℤ) (hd : d = gcd a b) : ∃ x y : ℤ, d = a * x + b * y   :=  by sorry
