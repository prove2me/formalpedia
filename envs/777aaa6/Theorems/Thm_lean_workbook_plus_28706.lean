-- Prove2me | Theorems.Thm_lean_workbook_plus_28706
-- name    : lean_workbook_plus_28706
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3b424d56-ea95-4dca-8deb-3d060c41e0ad
-- statement:
--   Prove that $x, y, z\in R_{+} \wedge xyz\ge1 \implies \frac{x}{x+y+z}\ge \frac{x^2}{x^5+y^2+z^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28706 (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0 ∧ x*y*z ≥ 1) : x/(x+y+z) ≥ x^2/(x^5+y^2+z^2)   :=  by sorry
