-- Prove2me | Theorems.Thm_lean_workbook_plus_1263
-- name    : lean_workbook_plus_1263
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b8909221-f0c4-4081-aaba-e5e859bb4bbe
-- statement:
--   Prove that $\sqrt{\frac{x^2+y^2+z^2}{3}} \ge \frac{x+y+z}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1263 (x y z : ℝ) :
  Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ≥ (x + y + z) / 3   :=  by sorry
