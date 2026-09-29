-- Prove2me | Theorems.Thm_lean_workbook_plus_13937
-- name    : lean_workbook_plus_13937
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4e6cef22-aa2d-43e3-99f0-02272d50b114
-- statement:
--   Prove that $3\,{\frac { \left( y-z \right) ^{2} \left( x-z \right) ^{2} \left( x-y \right) ^{2}}{{y}^{2}{x}^{2}{z}^{2}}}\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13937 (x y z : ℝ) : 3 * (y - z) ^ 2 * (x - z) ^ 2 * (x - y) ^ 2 / (y ^ 2 * x ^ 2 * z ^ 2) ≥ 0   :=  by sorry
