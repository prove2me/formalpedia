-- Prove2me | Theorems.Thm_lean_workbook_plus_56771
-- name    : lean_workbook_plus_56771
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/c3f79c84-ebb9-4234-988c-f492daf98ffe
-- statement:
--   Problema 6.\nSi $a_1, a_2, a_3 \geq 0$ y $(1 + a_1)(1 + a_2)(1 + a_3) = 8.$\nMostrar que:\n$a_1.a_2.a_3 \leq 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56771 (a₁ a₂ a₃ : ℝ) (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) (h₃ : 0 ≤ a₃) (h : (1 + a₁) * (1 + a₂) * (1 + a₃) = 8) : a₁ * a₂ * a₃ ≤ 1   :=  by sorry
