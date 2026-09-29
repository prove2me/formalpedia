-- Prove2me | Theorems.Thm_lean_workbook_plus_69201
-- name    : lean_workbook_plus_69201
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/e7112539-a159-4d3f-80d5-a1ff3638aa27
-- statement:
--   Prove that $(a_1^2 + a_2^2)(b_1^2 + b_2^2) \geq (a_1b_1 + a_2b_2)^2$ using Cauchy-Schwarz inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69201 (a₁ a₂ b₁ b₂ : ℝ) :
  (a₁^2 + a₂^2) * (b₁^2 + b₂^2) ≥ (a₁ * b₁ + a₂ * b₂)^2   :=  by sorry
