-- Prove2me | Theorems.Thm_lean_workbook_plus_11443
-- name    : lean_workbook_plus_11443
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3da7932d-73bb-45d8-9c67-b388908c87a2
-- statement:
--   Prove that $2x - 3y + 4z \leq 6$ for non-negative real numbers $x, y, z$ satisfying $3x + 5y + 7z = 10$ and $x + 2y + 5z = 6$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11443 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : 3*x + 5*y + 7*z = 10) (h' : x + 2*y + 5*z = 6) : 2*x - 3*y + 4*z ≤ 6   :=  by sorry
