-- Prove2me | Theorems.Thm_lean_workbook_plus_45523
-- name    : lean_workbook_plus_45523
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/87c17fdc-48c9-4ace-966e-f915d406c739
-- statement:
--   Check the cases $x,y,z\in \{0,1\}$ for the inequality $x^2+y^2+z^2\le x^2y+y^2z+z^2x+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45523 (x y z : ℕ) (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) : x^2 + y^2 + z^2 ≤ x^2 * y + y^2 * z + z^2 * x + 1   :=  by sorry
