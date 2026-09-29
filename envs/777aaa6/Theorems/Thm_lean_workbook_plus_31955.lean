-- Prove2me | Theorems.Thm_lean_workbook_plus_31955
-- name    : lean_workbook_plus_31955
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/eb64aeb5-9e4d-45d5-b023-6e31618d887c
-- statement:
--   Prove that $ (x^{2}+y^{2}+z^{2})^{3}\geq3(x^{2}y+y^{2}z+z^{2}x)^{2}$\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31955 (x y z : ℝ) : (x^2 + y^2 + z^2)^3 ≥ 3 * (x^2 * y + y^2 * z + z^2 * x)^2   :=  by sorry
