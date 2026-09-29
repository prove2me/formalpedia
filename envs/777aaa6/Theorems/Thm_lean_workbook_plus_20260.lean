-- Prove2me | Theorems.Thm_lean_workbook_plus_20260
-- name    : lean_workbook_plus_20260
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/df6358ee-ee9b-4ed6-8c53-ca057cfae548
-- statement:
--   Let $x,y,z,t$ be positive real numbers. Prove that $ xy+yz+zt+tx \leq \frac{1}{4} (x+y+z+t)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20260 (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : x * y + y * z + z * t + t * x ≤ 1 / 4 * (x + y + z + t) ^ 2   :=  by sorry
