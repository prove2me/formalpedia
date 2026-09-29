-- Prove2me | Theorems.Thm_lean_workbook_plus_57170
-- name    : lean_workbook_plus_57170
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/a6764a75-ab6f-48ba-82e6-fa0b47c1a4b3
-- statement:
--   Prove that $x^{5}+y^{5}+z^{5}\geq x^{2}+y^{2}+z^{2}$\nwhere x;y;z are real numbres greater than (-1) and satisfying $x^{3}+y^{3}+z^{3}\geq x^{2}+y^{2}+z^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57170 (x y z : ℝ) (hx : x > -1) (hy : y > -1) (hz : z > -1) (h : x^3 + y^3 + z^3 >= x^2 + y^2 + z^2) : x^5 + y^5 + z^5 >= x^2 + y^2 + z^2   :=  by sorry
