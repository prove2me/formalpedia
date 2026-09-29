-- Prove2me | Theorems.Thm_lean_workbook_plus_46738
-- name    : lean_workbook_plus_46738
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/32ed02f0-fc82-44ae-89f6-445fc19493c5
-- statement:
--   Let $\frac{a}{b}=x,\frac{b}{c}=y,\frac{c}{a}=z$ , then $x,y,z>0,xyz=1$ . Inequality becomes $(x+y+z)^2\ge3(xy+yz+zx)$ , that's obvious.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46738 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z = 1) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x)   :=  by sorry
