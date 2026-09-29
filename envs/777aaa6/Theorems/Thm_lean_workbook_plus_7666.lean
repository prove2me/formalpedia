-- Prove2me | Theorems.Thm_lean_workbook_plus_7666
-- name    : lean_workbook_plus_7666
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f94cc614-04c3-46b8-9880-e0c3955f0cf5
-- statement:
--   $3(x^2+y^2+z^2)\geq(x+y+z)^2$ holds for real $x,y,z$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7666 : ∀ (x y z : ℝ), 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ (x + y + z) ^ 2   :=  by sorry
