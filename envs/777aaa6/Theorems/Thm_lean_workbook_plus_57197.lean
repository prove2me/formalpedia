-- Prove2me | Theorems.Thm_lean_workbook_plus_57197
-- name    : lean_workbook_plus_57197
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/2355be6a-25c7-482d-8e1d-5c798b45c2ac
-- statement:
--   For any angles A, B and C, show that \n $ (cos\frac {A}{2} + cos\frac {B}{2} + cos\frac {C}{2})(tan\frac {A}{2} + tan\frac {B}{2} + tan\frac {C}{2} - tan\frac {A}{2}tan\frac {B}{2}tan\frac {C}{2})\ge4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57197 : ∀ (A B C : ℝ), (cos (A / 2) + cos (B / 2) + cos (C / 2)) * (tan (A / 2) + tan (B / 2) + tan (C / 2) - tan (A / 2) * tan (B / 2) * tan (C / 2)) ≥ 4   :=  by sorry
