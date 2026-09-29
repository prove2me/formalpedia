-- Prove2me | Theorems.Thm_lean_workbook_plus_51023
-- name    : lean_workbook_plus_51023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/7d20eb94-3801-44ee-b60e-e58148916a20
-- statement:
--   $ (x+y+z-3)[(x+y+z)^2+3(x+y+z)+36]\ge 0 \Rightarrow x+y+z \ge 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51023 : ∀ x y z : ℝ, (x+y+z-3)*((x+y+z)^2+3*(x+y+z)+36) ≥ 0 → x+y+z ≥ 3   :=  by sorry
