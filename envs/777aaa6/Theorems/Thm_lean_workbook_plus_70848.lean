-- Prove2me | Theorems.Thm_lean_workbook_plus_70848
-- name    : lean_workbook_plus_70848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/55e1e10e-f302-4924-927e-367049c87174
-- statement:
--   For the real numbers $ x \ge y \ge z \ge 0 $ prove that:\n$ 2(x^2 y+y^2 z + z^2 x +xyz) \ge (x+y)(y+z)(z+x) \ \ ; $\nGreetings!
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70848 (x y z : ℝ) (hxy : x ≥ y) (hyz : y ≥ z) (hz : z ≥ 0) : 2 * (x^2*y + y^2*z + z^2*x + x*y*z) ≥ (x + y) * (y + z) * (z + x)   :=  by sorry
