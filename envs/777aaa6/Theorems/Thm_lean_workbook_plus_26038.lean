-- Prove2me | Theorems.Thm_lean_workbook_plus_26038
-- name    : lean_workbook_plus_26038
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/64a294b6-bdf2-42fe-83b3-54e46d89d6c9
-- statement:
--   Prove that for positive $x, y, z$:\n$x+y+z \le 2\left(\dfrac {x^2}{y+z}+ \dfrac {y^2}{x+z}+ \dfrac {z^2}{x+y}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26038 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x + y + z ≤ 2 * (x^2 / (y + z) + y^2 / (x + z) + z^2 / (x + y))   :=  by sorry
