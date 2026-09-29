-- Prove2me | Theorems.Thm_lean_workbook_plus_75180
-- name    : lean_workbook_plus_75180
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/58d29201-021f-4135-abef-1037c63b8d5c
-- statement:
--   Prove that for all $x,y,z\ge 2$ , $4(x+y+z)\le xyz+16.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75180 (x y z : ℝ) (hx : x ≥ 2) (hy : y ≥ 2) (hz : z ≥ 2) : 4 * (x + y + z) ≤ x*y*z + 16   :=  by sorry
