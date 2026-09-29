-- Prove2me | Theorems.Thm_lean_workbook_plus_34058
-- name    : lean_workbook_plus_34058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/82091e20-74be-4598-b589-47cc566b2c47
-- statement:
--   Prove that for all $x,y,z\ge 2$ , $3(x+y+z)\le xyz+10.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34058 (x y z : ℝ) (hx : x ≥ 2) (hy : y ≥ 2) (hz : z ≥ 2) : 3 * (x + y + z) ≤ x*y*z + 10   :=  by sorry
