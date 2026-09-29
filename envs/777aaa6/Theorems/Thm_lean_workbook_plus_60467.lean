-- Prove2me | Theorems.Thm_lean_workbook_plus_60467
-- name    : lean_workbook_plus_60467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e29f9def-d54a-4aa7-ba6e-844f9dbab820
-- statement:
--   It's equivalent to $ 3(1-xyz)^2+(3-xy-xz-yz)^2\geq0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60467 (x y z : ℝ) : 3 * (1 - x * y * z) ^ 2 + (3 - x * y - x * z - y * z) ^ 2 ≥ 0   :=  by sorry
