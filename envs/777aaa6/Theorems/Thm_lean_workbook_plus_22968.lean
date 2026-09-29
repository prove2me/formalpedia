-- Prove2me | Theorems.Thm_lean_workbook_plus_22968
-- name    : lean_workbook_plus_22968
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b2081aea-4ad9-4c11-babe-c8dcabeccbae
-- statement:
--   $16r^2s^2(3r^2-s^2+4Rr+4R^2)\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22968 {r s R : ℝ} (h₁ : r ≥ 0 ∧ s ≥ 0 ∧ R ≥ 0) (h₂ : r ≤ s) (h₃ : s ≤ R + r) (h₄ : R ≤ s + r) : 16 * r ^ 2 * s ^ 2 * (3 * r ^ 2 - s ^ 2 + 4 * R * r + 4 * R ^ 2) ≥ 0   :=  by sorry
