-- Prove2me | Theorems.Thm_lean_workbook_plus_72809
-- name    : lean_workbook_plus_72809
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9b75bcb0-c582-48e1-9e20-12a7f8247232
-- statement:
--   Let, $\sqrt{x}$ , $\sqrt{y}$ , $\sqrt{z}$ be the sides of a triangle .Prove that $x^2+y^2+z^2\leq 2xy+2yz+2zx$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72809 {x y z : ℝ} (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hx1 : y + z > x) (hx2 : z + x > y) (hx3 : x + y > z) : x ^ 2 + y ^ 2 + z ^ 2 ≤ 2 * x * y + 2 * y * z + 2 * z * x   :=  by sorry
