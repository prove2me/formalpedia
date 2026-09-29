-- Prove2me | Theorems.Thm_lean_workbook_plus_20020
-- name    : lean_workbook_plus_20020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b603203f-06e4-4f68-9f61-5df0e719ec65
-- statement:
--   Find the maximum and minimum of $ A=x^2+y^2+z^2+kxyz $, where $ x, y, z $ are non-negative numbers satisfying $ x+y+z=1 $, for all $ k \in R $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20020 (x y z k : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hx1 : x + y + z = 1) : (x^2 + y^2 + z^2 + k * x * y * z) ≤ 1 + k/27 ∨ (x^2 + y^2 + z^2 + k * x * y * z) ≥ 1 + k/27   :=  by sorry
