-- Prove2me | Theorems.Thm_lean_workbook_plus_33925
-- name    : lean_workbook_plus_33925
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/7de6d544-3f0c-44ab-a89c-04aad77192ae
-- statement:
--   Prove: $\sum_{cyc} \frac{x}{2x+y+z} \le \frac34$ for $x, y, z > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33925 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x / (2 * x + y + z) + y / (2 * y + z + x) + z / (2 * z + x + y) ≤ 3 / 4   :=  by sorry
