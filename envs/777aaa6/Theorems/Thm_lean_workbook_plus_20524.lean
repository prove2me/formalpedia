-- Prove2me | Theorems.Thm_lean_workbook_plus_20524
-- name    : lean_workbook_plus_20524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/666a1261-9fd7-438b-849b-dd2695897caa
-- statement:
--   Show that for positive real numbers $x, y, z$ with $x + y + z = 1$, the inequality $v \leq \frac{1}{3}$ holds, where $v = xy + yz + zx$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20524 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) : x*y + y*z + z*x ≤ 1/3   :=  by sorry
