-- Prove2me | Theorems.Thm_lean_workbook_plus_58385
-- name    : lean_workbook_plus_58385
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5f21f3dc-78ff-437d-8030-1e57ba5ed257
-- statement:
--   Let $ x,y,z>0$ such as $ x+y+z=1$ and $ \frac{1}{x}+\frac{1}{y}+\frac{1}{z}+=1$ . Proove that $ x=1$ or $ y=1$ or $ z=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58385 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = 1) (h' : 1/x + 1/y + 1/z = 1) : x = 1 ∨ y = 1 ∨ z = 1   :=  by sorry
