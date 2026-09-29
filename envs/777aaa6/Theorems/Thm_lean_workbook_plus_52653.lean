-- Prove2me | Theorems.Thm_lean_workbook_plus_52653
-- name    : lean_workbook_plus_52653
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/15da6680-4d6f-43e2-9004-91bf7826d802
-- statement:
--   Prove that $-1<(x-1)(y-1)(z-1)<0$ for $0<x,y,z<1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52653 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) : -1 < (x - 1) * (y - 1) * (z - 1) ∧ (x - 1) * (y - 1) * (z - 1) < 0   :=  by sorry
