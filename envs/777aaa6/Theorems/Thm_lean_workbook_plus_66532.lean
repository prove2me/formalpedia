-- Prove2me | Theorems.Thm_lean_workbook_plus_66532
-- name    : lean_workbook_plus_66532
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/486acf20-68af-46c1-ae9e-8c41615f2b9e
-- statement:
--   (x - 1)(x - 3) $\ge$ 0 $\Rightarrow$ x $\in$ ( - $\infty$ ,1] $\cup$ [3,$\infty$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66532 (x : ℝ) (hx: (x - 1) * (x - 3) ≥ 0) :
  x ≤ 1 ∨ x ≥ 3   :=  by sorry
