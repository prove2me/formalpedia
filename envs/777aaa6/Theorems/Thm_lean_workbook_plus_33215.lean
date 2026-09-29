-- Prove2me | Theorems.Thm_lean_workbook_plus_33215
-- name    : lean_workbook_plus_33215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/206267e4-be79-4a24-9ff4-aa54432ce5a6
-- statement:
--   If $x_1x_2=bc$ and $x_2x_3=ac$ , then $x_2(x_1-x_3)=c(b-a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33215 (a b c x₁ x₂ x₃ : ℂ) (h₁ : x₁ * x₂ = b * c) (h₂ : x₂ * x₃ = a * c) : x₂ * (x₁ - x₃) = c * (b - a)   :=  by sorry
