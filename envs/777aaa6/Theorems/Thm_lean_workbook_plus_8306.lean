-- Prove2me | Theorems.Thm_lean_workbook_plus_8306
-- name    : lean_workbook_plus_8306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3d97614e-b3f5-4851-a6f1-deb88f34248d
-- statement:
--   $a^2+b^2+c^2=3\Rightarrow$ Let $x,y,z>0$ such that $a=\sqrt{\frac{3x}{x+y+z}}$ , $b=\sqrt{\frac{3y}{x+y+z}}$ and $c=\sqrt{\frac{3z}{x+y+z}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8306 (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hab : a + b + c = 3) (h : a = Real.sqrt (3 * x / (x + y + z))) (h' : b = Real.sqrt (3 * y / (x + y + z))) (h'' : c = Real.sqrt (3 * z / (x + y + z))) : a^2 + b^2 + c^2 = 3 → x^2 + y^2 + z^2 >= x * y + y * z + z * x   :=  by sorry
