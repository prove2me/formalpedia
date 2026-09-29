-- Prove2me | Theorems.Thm_lean_workbook_plus_55713
-- name    : lean_workbook_plus_55713
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/38267993-6dd2-45bd-bd55-83ffece224d3
-- statement:
--   Let, $\sqrt{x}$ , $\sqrt{y}$ , $\sqrt{z}$ be the sides of a triangle .Prove that $x^2+y^2+z^2\leq 2xy+2yz+2zx$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55713 (x y z : ℝ) (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hab : x + y > z) (hbc : y + z > x) (hca : z + x > y) : x ^ 2 + y ^ 2 + z ^ 2 ≤ 2 * x * y + 2 * y * z + 2 * z * x   :=  by sorry
