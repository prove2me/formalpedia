-- Prove2me | Theorems.Thm_lean_workbook_plus_55874
-- name    : lean_workbook_plus_55874
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/822b00ac-ad1f-4941-a3e1-2b83cc841eef
-- statement:
--   The inequality between the arithmetic mean and the quadratic mean gives $\frac{x+y+z}{3}\leq\sqrt{\frac{x^{2}+y^{2}+z^{2}}{3}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55874 (x y z : ℝ) :
  (x + y + z) / 3 ≤ Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3)   :=  by sorry
