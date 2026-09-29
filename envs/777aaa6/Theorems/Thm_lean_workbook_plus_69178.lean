-- Prove2me | Theorems.Thm_lean_workbook_plus_69178
-- name    : lean_workbook_plus_69178
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a7ecd18d-daa1-4b6f-a3e9-f1993630de1e
-- statement:
--   Let $a,b,c,x,y,z>0$ . Prove that $\frac{a^2}{x}+\frac{b^2}{y}+\frac{c^2}{z}\ge\frac{(a+b+c)^2}{x+y+z}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69178 (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (a^2 / x + b^2 / y + c^2 / z) ≥ (a + b + c)^2 / (x + y + z)   :=  by sorry
