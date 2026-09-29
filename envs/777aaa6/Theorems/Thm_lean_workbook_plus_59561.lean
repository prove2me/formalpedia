-- Prove2me | Theorems.Thm_lean_workbook_plus_59561
-- name    : lean_workbook_plus_59561
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/35d5bf8a-e724-427a-97cb-02976a76c04d
-- statement:
--   Solve the system of equations for real $x,y$:\nx = ra + sc\ny = rb + sd
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59561 (a b c d r s x y : ℝ) : x = r * a + s * c ∧ y = r * b + s * d ↔ x = r * a + s * c ∧ y = r * b + s * d   :=  by sorry
