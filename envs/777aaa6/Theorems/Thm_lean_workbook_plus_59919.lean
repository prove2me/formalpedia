-- Prove2me | Theorems.Thm_lean_workbook_plus_59919
-- name    : lean_workbook_plus_59919
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a352499f-c658-4c3c-bc00-2accdf237f32
-- statement:
--   Find all pairs of positive integers (x,y) such that: $x^2-6y^2=-3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59919 (x y : ℤ) (h₁ : 0 < x ∧ 0 < y) (h₂ : x^2 - 6*y^2 = -3) : x = 3 ∧ y = 1   :=  by sorry
