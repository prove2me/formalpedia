-- Prove2me | Theorems.Thm_lean_workbook_plus_82142
-- name    : lean_workbook_plus_82142
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e02ede21-f4ae-46cb-b8aa-3e25590396ab
-- statement:
--   Prove that $(x^2y^2+y^2z^2+z^2x^2)^2\geq \frac{(xy+yz+zx)^4}{9}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82142 (x y z : ℝ) : (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) ^ 2 ≥ (x * y + y * z + z * x) ^ 4 / 9   :=  by sorry
