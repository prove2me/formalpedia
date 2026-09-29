-- Prove2me | Theorems.Thm_lean_workbook_plus_33279
-- name    : lean_workbook_plus_33279
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/aafdb9f3-2b14-4c2a-8eea-c12a68f9d1ad
-- statement:
--   If $ x,y,z$ are positive numbers with $ \frac{x}{y} \ge \frac{1}{2},\frac{y}{z} \ge \frac{1}{2},\frac{z}{x} \ge \frac{1}{2}$ , then \n $ xyz \ge (2x-y)(2y-z)(2z-x).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33279 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x ≥ y / 2) (hyz : y ≥ z / 2) (hzx : z ≥ x / 2) :  x * y * z ≥ (2 * x - y) * (2 * y - z) * (2 * z - x)   :=  by sorry
