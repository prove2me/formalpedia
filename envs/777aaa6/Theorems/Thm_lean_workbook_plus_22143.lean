-- Prove2me | Theorems.Thm_lean_workbook_plus_22143
-- name    : lean_workbook_plus_22143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a28b9a0f-5a8f-40dd-84ef-974ebe66d096
-- statement:
--   Prove that $ x+y+z\leqslant 6$ given $ x,y,z\in R, 0<x\leq y\leq z\leq 3. yz\leq 6, xyz\leq 6.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22143 (x y z : ℝ) (hxy : 0 < x ∧ x ≤ y) (hyz : y ≤ z ∧ z ≤ 3) (h : y * z ≤ 6) (h' : x * y * z ≤ 6) : x + y + z ≤ 6   :=  by sorry
