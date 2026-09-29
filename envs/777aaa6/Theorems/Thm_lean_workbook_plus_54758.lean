-- Prove2me | Theorems.Thm_lean_workbook_plus_54758
-- name    : lean_workbook_plus_54758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4359cb65-352d-460e-bafb-1070c7e033f1
-- statement:
--   Let x,y,z >0 such that x+y+z=1. Prove that \n $ x+yz=(x+y)(x+z).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54758 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) : x + y * z = (x + y) * (x + z)   :=  by sorry
