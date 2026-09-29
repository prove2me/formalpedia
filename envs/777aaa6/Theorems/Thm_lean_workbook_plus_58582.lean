-- Prove2me | Theorems.Thm_lean_workbook_plus_58582
-- name    : lean_workbook_plus_58582
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f6970d8d-3858-419b-a2ad-4c1bb3d21704
-- statement:
--   So we just need to show that $x^2+y^2+z^2\geq xy+yz+zx$ , which is obvious since $\frac{1}{2}[(x-y)^2+(y-z)^2+(z-x)^2]\geq 0.\blacksquare$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58582 (x y z: ℝ) :  x * x + y * y + z * z ≥ x * y + y * z + z * x   :=  by sorry
