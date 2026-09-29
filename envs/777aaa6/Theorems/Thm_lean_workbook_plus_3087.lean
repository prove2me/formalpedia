-- Prove2me | Theorems.Thm_lean_workbook_plus_3087
-- name    : lean_workbook_plus_3087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f8486cde-d436-430d-90d6-df586d71f6c7
-- statement:
--   If $x,y,z>0$ P.T\n$x^4z^2+y^4x^2+z^4y^2\geq xyz(x^2z+y^2x+z^2y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3087 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 4 * z ^ 2 + y ^ 4 * x ^ 2 + z ^ 4 * y ^ 2 ≥ x * y * z * (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y)   :=  by sorry
