-- Prove2me | Theorems.Thm_lean_workbook_plus_78257
-- name    : lean_workbook_plus_78257
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d466529c-8e61-48c5-bb1e-945f2b3d70b2
-- statement:
--   Let $a,b,c$ be the lengths of a triangle sides. Prove that:\n $\sum_{cyc} a^2(b+c-a) \le 3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78257    (a b c : ℝ)
    (ha : 0 < a ∧ 0 < b ∧ 0 < c)
    (hab : a + b > c)
    (hbc : b + c > a)
    (hca : a + c > b) :
    a^2 * (b + c - a) + b^2 * (a + c - b) + c^2 * (a + b - c) ≤ 3 * a * b * c   :=  by sorry
