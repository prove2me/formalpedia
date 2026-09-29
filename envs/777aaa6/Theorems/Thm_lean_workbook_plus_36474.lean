-- Prove2me | Theorems.Thm_lean_workbook_plus_36474
-- name    : lean_workbook_plus_36474
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6b5da5d0-1f90-436d-8e71-a77f5626c70c
-- statement:
--   Let $a,b,c>0$ and $\dfrac{1}{a^2+1}+\dfrac{2}{ b^2+1}+\dfrac{2}{ c^2+1}=1.$ Prove that $$a+2b+ 2c\ge 10$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36474 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) : 1 / (a^2 + 1) + 2 / (b^2 + 1) + 2 / (c^2 + 1) = 1 → a + 2 * b + 2 * c ≥ 10   :=  by sorry
