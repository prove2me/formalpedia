-- Prove2me | Theorems.Thm_lean_workbook_plus_27506
-- name    : lean_workbook_plus_27506
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/39eab93b-a01d-40e6-a8c9-7a6b7483f868
-- statement:
--   Prove that if $ x+y+z=6$ and $ xy+yz+zx=9$ ( $ x,y,z\in\mathbb{R}$ ) then $ 0\le x,y,z\le 4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27506 (x y z : ℝ) (hx : x + y + z = 6) (hy : x * y + y * z + z * x = 9) : 0 ≤ x ∧ x ≤ 4 ∧ 0 ≤ y ∧ y ≤ 4 ∧ 0 ≤ z ∧ z ≤ 4   :=  by sorry
