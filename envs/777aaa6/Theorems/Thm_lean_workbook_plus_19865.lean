-- Prove2me | Theorems.Thm_lean_workbook_plus_19865
-- name    : lean_workbook_plus_19865
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f960df5b-9434-4fac-b9aa-9e61ef96600f
-- statement:
--   If $ x,y,z \in \mathbb{R}$ and $ x^3+y^3+z^3=3xyz$ then $ x+y+z=0$ or $ x=y=z.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19865 (x y z : ℝ) (h : x^3 + y^3 + z^3 = 3 * x * y * z) :  x + y + z = 0 ∨ x = y ∧ y = z   :=  by sorry
