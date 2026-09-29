-- Prove2me | Theorems.Thm_lean_workbook_plus_55363
-- name    : lean_workbook_plus_55363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/83a58812-e2d3-452d-8744-985f1952eea6
-- statement:
--   Prove or disprove: For all real numbers $a_1,a_2,a_3,b,c,d$ : $a_1^2+a_2^2+a_3^2+b^2+c^2+d^2\ge2(a_1a_3+a_1a_2-a_2a_3+bc+bd-cd)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55363 : ∀ a₁ a₂ a₃ b c d : ℝ, a₁^2 + a₂^2 + a₃^2 + b^2 + c^2 + d^2 ≥ 2 * (a₁ * a₃ + a₁ * a₂ - a₂ * a₃ + b * c + b * d - c * d)   :=  by sorry
