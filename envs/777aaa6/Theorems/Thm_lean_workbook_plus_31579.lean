-- Prove2me | Theorems.Thm_lean_workbook_plus_31579
-- name    : lean_workbook_plus_31579
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/bf6deb19-dd4c-49fb-9084-c7d3649e4e8e
-- statement:
--   Let $x+y+z=T_1; xy+yz+zx=T_2; xyz=T_3$ . Prove that $(x-y)^2(y-z)^2(z-x)^2=T_1^2T_2^2 + 18{T_1}{T_2}{T_3} - 4T_1^3{T_3} - 4T_2^3 - 27T_3^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31579 {x y z T1 T2 T3 : ℝ} (hx : x + y + z = T1) (hy : x*y + y*z + z*x = T2) (hz : x*y*z = T3) : (x - y) ^ 2 * (y - z) ^ 2 * (z - x) ^ 2 = T1 ^ 2 * T2 ^ 2 + 18*T1*T2*T3 - 4*T1 ^ 3 * T3 - 4*T2 ^ 3 - 27*T3 ^ 2   :=  by sorry
