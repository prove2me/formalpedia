-- Prove2me | Theorems.Thm_lean_workbook_plus_77089
-- name    : lean_workbook_plus_77089
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/3381fb24-67f8-4ef5-b380-11c4ef744c81
-- statement:
--   Prove that if $d = gcd(a, b)$, then $d$ divides any linear combination of $a$ and $b$, i.e., $d | (ax+by) \forall x, y \in \mathbb{Z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77089 (a b d x y : ℤ) (h₁ : d = gcd a b) : d ∣ a * x + b * y   :=  by sorry
