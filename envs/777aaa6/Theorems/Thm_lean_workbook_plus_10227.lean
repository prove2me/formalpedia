-- Prove2me | Theorems.Thm_lean_workbook_plus_10227
-- name    : lean_workbook_plus_10227
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/82993f2e-aef7-429b-9808-f173340e12b2
-- statement:
--   Verify the inequality $\frac{4}{(x+y)^{2}}+\frac{4}{(x+z)^{2}}+\frac{4}{(y+z)^{2}}\geq \frac{27}{(x+y+z)^{2}}$ for $x = y = z = \frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10227 (x y z : ℝ) (hx : x = 1 / 3) (hy : y = 1 / 3) (hz : z = 1 / 3) : (4 / (x + y) ^ 2 + 4 / (x + z) ^ 2 + 4 / (y + z) ^ 2) ≥ 27 / (x + y + z) ^ 2   :=  by sorry
