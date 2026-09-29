-- Prove2me | Theorems.Thm_lean_workbook_plus_74137
-- name    : lean_workbook_plus_74137
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/588864db-37c4-4b53-8fa3-dddd6b768fba
-- statement:
--   For three arbitrary positive real numbers $ x,y,z$ such that $ x + y + z + 4xyz = 1$ , prove that $ xy + yz + zx \leq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74137 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x + y + z + 4*x*y*z = 1) : x*y + y*z + z*x ≤ 1   :=  by sorry
