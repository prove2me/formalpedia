-- Prove2me | Theorems.Thm_lean_workbook_plus_7481
-- name    : lean_workbook_plus_7481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8b04b4c7-1f7e-48f9-b551-e0c639c5d8af
-- statement:
--   Let $ x$ , $ y$ , $ z$ be real numbers such that $ 0 < x,y,z < 1$ and $ xyz = (1 - x)(1 - y)(1 - z)$ . Show that at least one of the numbers $ (1 - x)y,(1 - y)z,(1 - z)x$ is greater than or equal to $ \frac {1}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7481 (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) (hab : x*y*z = (1 - x)*(1 - y)*(1 - z)) : (1 - x)*y ≥ 1/4 ∨ (1 - y)*z ≥ 1/4 ∨ (1 - z)*x ≥ 1/4   :=  by sorry
