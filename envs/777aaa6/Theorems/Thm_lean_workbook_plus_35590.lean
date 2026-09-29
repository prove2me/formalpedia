-- Prove2me | Theorems.Thm_lean_workbook_plus_35590
-- name    : lean_workbook_plus_35590
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/ed05525b-6889-44c7-ada5-9b7e4babe41d
-- statement:
--   Given complex numbers $z_1 = a + ib$ and $z_2 = c + id$, prove that $|z_1 z_2| = |z_1| |z_2|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35590 (a b c d : ℝ) : ‖(a + b * I) * (c + d * I)‖ = ‖a + b * I‖ * ‖c + d * I‖   :=  by sorry
