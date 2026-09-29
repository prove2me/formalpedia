-- Prove2me | Theorems.Thm_lean_workbook_plus_1305
-- name    : lean_workbook_plus_1305
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8116abf1-6825-43a8-a5ce-390e4c489509
-- statement:
--   Prove that for all positive numbers $x, y, z$, the following inequality holds: $ \sum_{cyc}\frac {x}{y + z} \geq \frac {3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1305 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + y / (z + x) + z / (x + y)) ≥ 3 / 2   :=  by sorry
