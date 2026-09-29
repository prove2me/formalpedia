-- Prove2me | Theorems.Thm_lean_workbook_plus_66158
-- name    : lean_workbook_plus_66158
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c80670d7-8567-4136-91e1-29136710943e
-- statement:
--   Prove that for every $0<x,y<1$:\nx\ge y\implies x^n \ge y^n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66158 (n : ℕ) (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hxy : x ≥ y) : x^n ≥ y^n   :=  by sorry
