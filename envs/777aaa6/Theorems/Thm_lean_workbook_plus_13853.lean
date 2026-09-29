-- Prove2me | Theorems.Thm_lean_workbook_plus_13853
-- name    : lean_workbook_plus_13853
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/949f791b-6aa3-4e5b-bf19-89aeddcf2a86
-- statement:
--   For $x\ge y\ge z$ or $x\ge z\ge y$ and $x,y,z>0$, prove that $x^3+y^3+z^3+2(x^2y+y^2z+z^2x)\ge 3(x^2y+y^2z+z^2x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13853 (x y z : ℝ) (h : x ≥ y ∧ y ≥ z ∨ x ≥ z ∧ z ≥ y) (hx : 0 < x ∧ 0 < y ∧ 0 < z) : x^3 + y^3 + z^3 + 2 * (x^2 * y + y^2 * z + z^2 * x) ≥ 3 * (x^2 * y + y^2 * z + z^2 * x)   :=  by sorry
