-- Prove2me | Theorems.Thm_lean_workbook_plus_10967
-- name    : lean_workbook_plus_10967
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/7f13ca68-bbad-42b2-a81e-d2a0b3a599e7
-- statement:
--   find the condition for equality: $x=y=z=\frac{1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10967 (x y z : ℝ) : x = y ∧ y = z ∧ z = 1 / 3 ↔ x = y ∧ y = z ∧ z = 1 / 3   :=  by sorry
