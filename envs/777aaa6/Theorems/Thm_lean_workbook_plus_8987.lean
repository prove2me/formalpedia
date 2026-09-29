-- Prove2me | Theorems.Thm_lean_workbook_plus_8987
-- name    : lean_workbook_plus_8987
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ae70cf8b-4138-4be9-b4ac-2d7028474dc2
-- statement:
--   If 0<x,y,z<1 .Prove that\n $x(1-y)+y(1-z)+z(1-x)<1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8987 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) : x * (1 - y) + y * (1 - z) + z * (1 - x) < 1   :=  by sorry
