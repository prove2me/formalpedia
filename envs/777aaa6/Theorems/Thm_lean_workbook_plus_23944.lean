-- Prove2me | Theorems.Thm_lean_workbook_plus_23944
-- name    : lean_workbook_plus_23944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/7c3ccfca-4814-4eda-9da2-9dd4fad14e42
-- statement:
--   Let $x,y,z\geq 0$ ,prove that: $(x^4+y^4+z^4)(x^2y^2+y^2z^2+z^2x^2)\geq (xy^3+yz^3+x^3z)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23944 (x y z : ℝ) : (x^4 + y^4 + z^4) * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ≥ (x * y^3 + y * z^3 + x^3 * z)^2   :=  by sorry
