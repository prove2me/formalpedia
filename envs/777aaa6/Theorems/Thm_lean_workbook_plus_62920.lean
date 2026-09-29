-- Prove2me | Theorems.Thm_lean_workbook_plus_62920
-- name    : lean_workbook_plus_62920
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0847557b-ea9f-483e-9d1f-16252485a026
-- statement:
--   Using the rearrangement inequality, prove that \(x/yz + y/xz + z/xy \geq 1/x + 1/y + 1/z\) for positive numbers $x, y, z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62920 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x / y / z + y / z / x + z / x / y ≥ 1 / x + 1 / y + 1 / z   :=  by sorry
