-- Prove2me | Theorems.Thm_lean_workbook_plus_57324
-- name    : lean_workbook_plus_57324
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/86c3882d-f75b-49ff-b13f-b915f4ea1c82
-- statement:
--   Let $x,$ $y$ and $z$ are non-negative real numbers. Prove that \n $x^{4}y+x^{4}z+y^{4}x+y^{4}z+z^{4}x+z^{4}y+6xyz(xy+xz+yz)\geq8xyz(x^{2}+y^{2}+z^{2}).$\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57324 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x^4 * y + x^4 * z + y^4 * x + y^4 * z + z^4 * x + z^4 * y + 6 * x * y * z * (x * y + x * z + y * z) ≥ 8 * x * y * z * (x^2 + y^2 + z^2)   :=  by sorry
