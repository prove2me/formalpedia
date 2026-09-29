-- Prove2me | Theorems.Thm_lean_workbook_plus_43677
-- name    : lean_workbook_plus_43677
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/039fba3f-9e43-4ab4-91ec-edd3e0e4ddf9
-- statement:
--   Prove that $(x+y+z)+3xyz\geq 2(xy+yz+zx)$ given $0\leq x,y,z\leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43677 (x y z : ℝ) (hx: x ∈ Set.Icc 0 1) (hy: y ∈ Set.Icc 0 1) (hz: z ∈ Set.Icc 0 1): (x+y+z)+3*x*y*z ≥ 2*(x*y + y*z + z*x)   :=  by sorry
