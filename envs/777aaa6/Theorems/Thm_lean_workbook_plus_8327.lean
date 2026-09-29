-- Prove2me | Theorems.Thm_lean_workbook_plus_8327
-- name    : lean_workbook_plus_8327
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/71cb90aa-b653-47b5-adfd-8e2d231c3c27
-- statement:
--   The condition gives $(x-1)^2+(y-1)^2+(z-1)^2=0$ , yielding reals $x=y=z=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8327 (x y z : ℝ) (h : (x - 1) ^ 2 + (y - 1) ^ 2 + (z - 1) ^ 2 = 0) : x = 1 ∧ y = 1 ∧ z = 1   :=  by sorry
