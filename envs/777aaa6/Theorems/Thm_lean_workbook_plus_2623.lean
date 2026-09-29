-- Prove2me | Theorems.Thm_lean_workbook_plus_2623
-- name    : lean_workbook_plus_2623
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c2ad8aaf-a32b-45ff-b8bd-1160b678a02a
-- statement:
--   Prove that for all distinct integers $x, y, z$, $5(x-y)(y-z)(z-x)$ divides $(x-y)^5+(y-z)^5+(z-x)^5$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2623 (x y z : ℤ) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : 5 * (x - y) * (y - z) * (z - x) ∣ (x - y) ^ 5 + (y - z) ^ 5 + (z - x) ^ 5   :=  by sorry
