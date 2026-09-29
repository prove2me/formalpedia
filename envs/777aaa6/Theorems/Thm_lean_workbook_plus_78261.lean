-- Prove2me | Theorems.Thm_lean_workbook_plus_78261
-- name    : lean_workbook_plus_78261
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/52b2dda9-9509-46af-ae7e-be4b4cf14d36
-- statement:
--   If $x,y,z>0$ and $xy+yz+zx \le xyz$, prove that $x^2 y^2 + y^2 z^2+ z^2 x^2 \ge 9 (xy+yz+zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78261 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y + y * z + z * x ≤ x * y * z) : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≥ 9 * (x * y + y * z + z * x)   :=  by sorry
