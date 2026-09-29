-- Prove2me | Theorems.Thm_lean_workbook_plus_63964
-- name    : lean_workbook_plus_63964
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/51d6f78e-140b-441d-b977-5a490b7c3bd7
-- statement:
--   For $ x, y, z > 0 $ real numbers, prove that:\n$ \frac{1}{12} \sum\limits_{cyc} \,x \left( 3\,{x}^{2}+2\,yz \right) \left( x+y-2\,z \right) ^{2}+\frac{3}{4} \sum\limits_{cyc} \,x \left( {x}^{2}+4\,{y}^{2} \right) \left( x-y \right) ^{2}+3\, \sum\limits_{cyc} x \left( x-y \right) ^{2} \left( x+y-z \right) ^{2} \geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63964 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / 12 * (x * (3 * x ^ 2 + 2 * y * z) * (x + y - 2 * z) ^ 2 + y * (3 * y ^ 2 + 2 * z * x) * (y + z - 2 * x) ^ 2 + z * (3 * z ^ 2 + 2 * x * y) * (z + x - 2 * y) ^ 2) + 3 / 4 * (x * (x ^ 2 + 4 * y ^ 2) * (x - y) ^ 2 + y * (y ^ 2 + 4 * z ^ 2) * (y - z) ^ 2 + z * (z ^ 2 + 4 * x ^ 2) * (z - x) ^ 2) + 3 * (x * (x - y) ^ 2 * (x + y - z) ^ 2 + y * (y - z) ^ 2 * (y + z - x) ^ 2 + z * (z - x) ^ 2 * (z + x - y) ^ 2) ≥ 0   :=  by sorry
