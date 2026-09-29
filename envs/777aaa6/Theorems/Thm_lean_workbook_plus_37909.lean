-- Prove2me | Theorems.Thm_lean_workbook_plus_37909
-- name    : lean_workbook_plus_37909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a6ec6b53-cd86-45b6-a9ae-c4a834354197
-- statement:
--   Prove that $(3x+4y+5z)^2\geq24(3yz+2xz+xy)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37909 : ∀ x y z : ℝ, (3*x+4*y+5*z)^2 ≥ 24*(3*y*z+2*x*z+x*y)   :=  by sorry
