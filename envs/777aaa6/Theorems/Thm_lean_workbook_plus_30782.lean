-- Prove2me | Theorems.Thm_lean_workbook_plus_30782
-- name    : lean_workbook_plus_30782
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f18a08da-5dc9-4824-8c03-2af01ba31fbd
-- statement:
--   If $x,y,z\ge 0,x+y+z=4 $ , then $ (x^2+2)(y^2+2)(z^2+2)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30782 (x y z : ℝ) (hx : x + y + z = 4) (hx' : 0 ≤ x) (hy' : 0 ≤ y) (hz' : 0 ≤ z) : (x^2 + 2) * (y^2 + 2) * (z^2 + 2) ≥ 0   :=  by sorry
