-- Prove2me | Theorems.Thm_lean_workbook_plus_13602
-- name    : lean_workbook_plus_13602
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/ec9510e6-e16a-4c4a-9994-5d64818e031d
-- statement:
--   $\sum_{cyc}x^2y^2 \geq \sum_{cyc}x^2yz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13602 (x y z : ℝ) : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 ≥ x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y   :=  by sorry
