-- Prove2me | Theorems.Thm_lean_workbook_plus_10449
-- name    : lean_workbook_plus_10449
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2716b00e-491c-4bf2-9525-35023e37d7f5
-- statement:
--   Find all integers a such that $\frac{a}{2}+1$ and $\frac{a}{3}$ are perfect squares.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10449 (a : ℤ) (h1 : ∃ x : ℤ, x^2 = a/2 + 1) (h2 : ∃ y : ℤ, y^2 = a/3) : ∃ x y : ℤ, x^2 = a/2 + 1 ∧ y^2 = a/3   :=  by sorry
