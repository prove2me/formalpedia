-- Prove2me | Theorems.Thm_lean_workbook_plus_26494
-- name    : lean_workbook_plus_26494
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d519ea30-a0ba-4306-aa31-c43a5cf0d43e
-- statement:
--   prove that: \n\n $\frac{2}{3}(x+y+z)\geq(y+x)(y+z)(z+x)$\n\n$x,y,z \in (0,\frac{1}{2}]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26494 (x y z : ℝ) (hx : x ∈ Set.Icc 0 (1 / 2)) (hy : y ∈ Set.Icc 0 (1 / 2)) (hz : z ∈ Set.Icc 0 (1 / 2)) : (2 / 3) * (x + y + z) ≥ (y + x) * (y + z) * (z + x)   :=  by sorry
