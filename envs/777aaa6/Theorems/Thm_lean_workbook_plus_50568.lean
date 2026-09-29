-- Prove2me | Theorems.Thm_lean_workbook_plus_50568
-- name    : lean_workbook_plus_50568
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/70899bb5-cf4a-4195-b048-222439f293a5
-- statement:
--   Let $ u=\sqrt{x}$ , then it is $ 2u^3+y^3\ge 3u^2y\iff (u-y)^2(2u+y)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50568 (x y : ℝ) : 2 * (Real.sqrt x) ^ 3 + y ^ 3 ≥ 3 * (Real.sqrt x) ^ 2 * y ↔ (Real.sqrt x - y) ^ 2 * (2 * Real.sqrt x + y) ≥ 0   :=  by sorry
