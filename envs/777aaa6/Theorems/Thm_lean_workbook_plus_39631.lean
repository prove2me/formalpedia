-- Prove2me | Theorems.Thm_lean_workbook_plus_39631
-- name    : lean_workbook_plus_39631
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a645023d-7edf-4d9a-82a3-da086f693d14
-- statement:
--   Let $x;y;z$ be positive real numbers. Prove that: $x^{2}(y+z)+y^{2}(x+z)+z^{2}(x+y)\ge 6xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39631 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^2 * (y + z) + y^2 * (x + z) + z^2 * (x + y) >= 6 * x * y * z   :=  by sorry
