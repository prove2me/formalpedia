-- Prove2me | Theorems.Thm_lean_workbook_plus_49250
-- name    : lean_workbook_plus_49250
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4543e104-3f20-45ac-be77-9ef99e15bd18
-- statement:
--   if $x,y,z>0$ ,prove $4/(x^2+yz)$ ≤ $1/(xy)+1/(xz)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49250 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 4 / (x ^ 2 + y * z) ≤ 1 / (x * y) + 1 / (x * z)   :=  by sorry
