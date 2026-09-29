-- Prove2me | Theorems.Thm_lean_workbook_plus_5538
-- name    : lean_workbook_plus_5538
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/07a2e26c-e686-49fd-b8a9-166af6b9761d
-- statement:
--   Let $x,y,z>0$ and $xyz=1$ . Prove that: \n $\frac{1}{1+x+x^2}+\frac{1}{1+y+y^2}+\frac{1}{1+z+z^2}\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5538 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x * y * z = 1) : 1 / (1 + x + x^2) + 1 / (1 + y + y^2) + 1 / (1 + z + z^2) ≥ 1   :=  by sorry
