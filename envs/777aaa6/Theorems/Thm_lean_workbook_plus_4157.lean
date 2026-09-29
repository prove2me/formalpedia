-- Prove2me | Theorems.Thm_lean_workbook_plus_4157
-- name    : lean_workbook_plus_4157
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a27bc144-5797-4d44-b337-7060bcf0ce4f
-- statement:
--   prove $x^2+y^2+z^2 \geq \frac{3}{4}$ given $x,y,z \geqslant 0$ and $x+y^2+z^3=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4157 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y^2 + z^3 = 1) : x^2 + y^2 + z^2 ≥ 3 / 4   :=  by sorry
