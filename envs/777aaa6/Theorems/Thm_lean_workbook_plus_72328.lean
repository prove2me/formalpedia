-- Prove2me | Theorems.Thm_lean_workbook_plus_72328
-- name    : lean_workbook_plus_72328
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/735d5584-f0ba-4a44-b9f6-b5ccfce3b88b
-- statement:
--   Let there be x and y positive numbers. Prove that $x+y\geq2\sqrt{xy}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72328 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x + y ≥ 2 * Real.sqrt (x * y)   :=  by sorry
