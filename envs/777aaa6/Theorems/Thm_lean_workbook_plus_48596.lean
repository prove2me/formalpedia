-- Prove2me | Theorems.Thm_lean_workbook_plus_48596
-- name    : lean_workbook_plus_48596
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/47718394-f510-4e1c-b061-10a08a05658e
-- statement:
--   If $a>b>c$ are real numbers prove that $\frac{1}{a-b}+\frac{1}{b-c}>\frac{2}{a-c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48596 (a b c : ℝ) (h₁ : a > b) (h₂ : b > c) : 1 / (a - b) + 1 / (b - c) > 2 / (a - c)   :=  by sorry
