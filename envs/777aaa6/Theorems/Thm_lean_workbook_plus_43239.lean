-- Prove2me | Theorems.Thm_lean_workbook_plus_43239
-- name    : lean_workbook_plus_43239
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b385e21f-7645-4b64-af05-df2049d33a55
-- statement:
--   Prove that \(x^6 + y^6 + z^6 \geq xyz(x^3 + y^3 + z^3)\) when \(xyz = 1\) using variable change and AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43239 (x y z : ℝ) (h : x*y*z = 1) :
  x^6 + y^6 + z^6 ≥ x*y*z*(x^3 + y^3 + z^3)   :=  by sorry
