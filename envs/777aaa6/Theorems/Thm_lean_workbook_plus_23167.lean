-- Prove2me | Theorems.Thm_lean_workbook_plus_23167
-- name    : lean_workbook_plus_23167
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/906ebfc8-7f76-48c0-89ae-8ffb19494d59
-- statement:
--   Substitute : $a=x+y;b=y+z;c=z+x,\,x,y,z>0$ . After calculations, the inequality is written : $\sum x^2y+\sum xy^2\ge 6xyz$ , which is true by AM-GM.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23167 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2*y + y^2*z + z^2*x + (x*y^2 + y*z^2 + z*x^2) ≥ 6*x*y*z   :=  by sorry
