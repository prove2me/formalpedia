-- Prove2me | Theorems.Thm_lean_workbook_plus_27487
-- name    : lean_workbook_plus_27487
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/0765f79f-8026-4c65-9cc4-5253dee419cc
-- statement:
--   Let $x,y,z,t$ be positive real numbers. Prove that $ xy+yz+zt+tx \leq \frac{1}{4} (x+y+z+t)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27487 (x y z t : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (ht : t > 0) : x * y + y * z + z * t + t * x ≤ 1 / 4 * (x + y + z + t) ^ 2   :=  by sorry
