-- Prove2me | Theorems.Thm_lean_workbook_plus_10544
-- name    : lean_workbook_plus_10544
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c8f61e04-e24e-4f10-b9f0-34b6a83aa8ea
-- statement:
--   For any angles A, B and C, show that \n $ (cos\frac {A}{2} + cos\frac {B}{2} + cos\frac {C}{2})(tan\frac {A}{2} + tan\frac {B}{2} + tan\frac {C}{2} - tan\frac {A}{2}tan\frac {B}{2}tan\frac {C}{2})\ge4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10544 : ∀ (A B C : ℝ), (cos (A / 2) + cos (B / 2) + cos (C / 2)) * (tan (A / 2) + tan (B / 2) + tan (C / 2) - tan (A / 2) * tan (B / 2) * tan (C / 2)) >= 4   :=  by sorry
