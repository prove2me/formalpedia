-- Prove2me | Theorems.Thm_lean_workbook_plus_73565
-- name    : lean_workbook_plus_73565
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/95e39e1d-1bc2-4696-9afc-53efa3e8030a
-- statement:
--   Given that $xy = \dfrac32$ and both $x$ and $y$ are nonnegative real numbers, find the minimum value of $10x + \dfrac{3y}5.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73565 (x y : ℝ) (h₁ : x * y = 3 / 2) (h₂ : 0 ≤ x) (h₃ : 0 ≤ y) : 6 ≤ 10 * x + 3 * y / 5   :=  by sorry
