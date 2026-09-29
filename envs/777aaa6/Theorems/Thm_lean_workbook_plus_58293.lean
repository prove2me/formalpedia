-- Prove2me | Theorems.Thm_lean_workbook_plus_58293
-- name    : lean_workbook_plus_58293
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/be5c417a-35b6-41c9-9654-555d8629773c
-- statement:
--   $0<x<1$ implies $x^{2}> x^{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58293 (x : ℝ) (hx : 0 < x ∧ x < 1) : x^2 > x^5   :=  by sorry
