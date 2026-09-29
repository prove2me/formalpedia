-- Prove2me | Theorems.Thm_lean_workbook_plus_3919
-- name    : lean_workbook_plus_3919
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6109f85d-2ade-46e3-994d-a61350948f12
-- statement:
--   Let $x,y,z\leq{0}$ and $xyz=1$ . Prove that: $x+y+z\leq{x^{2}+y^{2}+z^{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3919 (x y z : ℝ) (h : x ≤ 0 ∧ y ≤ 0 ∧ z ≤ 0 ∧ x * y * z = 1) :
  x + y + z ≤ x ^ 2 + y ^ 2 + z ^ 2   :=  by sorry
