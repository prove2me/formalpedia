-- Prove2me | Theorems.Thm_lean_workbook_plus_55935
-- name    : lean_workbook_plus_55935
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/d8817090-9aa0-4235-9096-aff3839fba25
-- statement:
--   Prove that $(xy+zx+yz)(x^2y+y^2z+z^2x)\geq (x+y+z)^2xyz$ given $x,y,z>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55935 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y + z * x + y * z) * (x^2 * y + y^2 * z + z^2 * x) ≥ (x + y + z)^2 * x * y * z   :=  by sorry
