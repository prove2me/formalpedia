-- Prove2me | Theorems.Thm_lean_workbook_plus_50554
-- name    : lean_workbook_plus_50554
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3a8441c6-3b1d-49e4-9d41-961cf6738d8b
-- statement:
--   Prove the inequality $a+1 \geq 2\sqrt{a}$ using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50554 (a : ℝ) (ha : a ≥ 0) : a + 1 ≥ 2 * Real.sqrt a   :=  by sorry
