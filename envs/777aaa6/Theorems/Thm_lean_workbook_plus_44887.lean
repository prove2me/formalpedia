-- Prove2me | Theorems.Thm_lean_workbook_plus_44887
-- name    : lean_workbook_plus_44887
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/de1b28b9-0777-4092-98c1-ecc67f20b125
-- statement:
--   Given the points A(0,-5), B(1,7), C(-3/2,-23), and D(-3,-41) on the curve $y = 2x^4 + 7x^3 + 3x - 5$, find the arithmetic mean of the x-coordinates of these points.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44887 (A B C D : ℝ × ℝ) (hA : A = (0,-5)) (hB : B = (1,7)) (hC : C = (-3/2,-23)) (hD : D = (-3,-41)) (h : ∀ p : ℝ × ℝ, p ∈ ({A, B, C, D} : Finset (ℝ × ℝ))) : (A.1 + B.1 + C.1 + D.1) / 4 = -7/8   :=  by sorry
