-- Prove2me | Theorems.Thm_lean_workbook_plus_36220
-- name    : lean_workbook_plus_36220
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/454fc0f8-97f8-4da2-981c-3f4e5bc80222
-- statement:
--   and we use C.B.S. and the inequality is equivalent to $x^2y^2+x^2z^2+y^2z^2\ge xyz(x+y+z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36220 (x y z : ℝ) : x^2*y^2 + x^2*z^2 + y^2*z^2 ≥ x*y*z*(x + y + z)   :=  by sorry
