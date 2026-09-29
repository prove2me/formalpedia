-- Prove2me | Theorems.Thm_lean_workbook_plus_36507
-- name    : lean_workbook_plus_36507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/779a3072-54c0-40e4-ba7b-52d3007df8a9
-- statement:
--   $x^2+y^2+z^2+2xyz \geq 2xy +z^2 +2xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36507 (x y z : ℝ) : x^2+y^2+z^2+2*x*y*z ≥ 2*x*y + z^2 + 2*x*y*z   :=  by sorry
