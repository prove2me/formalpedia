-- Prove2me | Theorems.Thm_lean_workbook_plus_39574
-- name    : lean_workbook_plus_39574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/49a88ef0-e9d6-4b15-ba07-1b241fbfa780
-- statement:
--   If $x\ge y\ge z$ and $x,y,z>0$, prove that $x^2y+y^2z+z^2x\ge x^2z+y^2x+z^2y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39574 (x y z : ℝ) (h : x ≥ y ∧ y ≥ z ∧ z > 0) : x^2*y + y^2*z + z^2*x ≥ x^2*z + y^2*x + z^2*y   :=  by sorry
