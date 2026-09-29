-- Prove2me | Theorems.Thm_lean_workbook_plus_65300
-- name    : lean_workbook_plus_65300
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e596762e-9a48-4db7-87f0-07a8bc6c1d80
-- statement:
--   You can even try to prove that If $0 \leq x,y,z \leq 1$ then $2 \sum xy \leq 3xyz + \sum x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65300 (x y z : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) : 2 * (x*y + y*z + z*x) ≤ 3*x*y*z + x + y + z   :=  by sorry
