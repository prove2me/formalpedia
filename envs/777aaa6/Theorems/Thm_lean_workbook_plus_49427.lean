-- Prove2me | Theorems.Thm_lean_workbook_plus_49427
-- name    : lean_workbook_plus_49427
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c964f646-d7ce-4194-bb3e-8ce055fd23ca
-- statement:
--   If $x,y,z\in \mathbb{R}^+,$ prove that $(x^3+y^3+z^3)^2\ge \frac 98(x^2+yz)(y^2+zx)(z^2+xy)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49427 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3)^2 ≥ (9/8)*(x^2 + y*z)*(y^2 + z*x)*(z^2 + x*y)   :=  by sorry
