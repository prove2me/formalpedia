-- Prove2me | Theorems.Thm_lean_workbook_plus_49995
-- name    : lean_workbook_plus_49995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/314fbb9b-a476-4aff-b228-e5af718eda2d
-- statement:
--   Parametrization (Ramanujan): $w=6n^2-4nm+4m^2$ $x=3n^2+5nm-5m^2$ $y=4n^2-4nm+6m^2$ $z=5n^2-5nm-3m^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49995 (n m : ℤ) : ∃ w x y z : ℤ, w = 6*n^2 - 4*n*m + 4*m^2 ∧ x = 3*n^2 + 5*n*m - 5*m^2 ∧ y = 4*n^2 - 4*n*m + 6*m^2 ∧ z = 5*n^2 - 5*n*m - 3*m^2   :=  by sorry
