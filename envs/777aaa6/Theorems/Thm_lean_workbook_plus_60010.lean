-- Prove2me | Theorems.Thm_lean_workbook_plus_60010
-- name    : lean_workbook_plus_60010
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/fc5ca208-842c-47be-ac42-f8104be8a7d1
-- statement:
--   prove that: $(x+y-z)(z+x-y)(x-y)(x-z)+(y+z-x)(x+y-z)(y-z)(y-x)+(z+x-y)(y+z-x)(z-x)(z-y)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60010 (x y z : ℝ) :
  (x + y - z) * (z + x - y) * (x - y) * (x - z) + (y + z - x) * (x + y - z) * (y - z) * (y - x) + (z + x - y) * (y + z - x) * (z - x) * (z - y) ≥ 0   :=  by sorry
