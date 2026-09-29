-- Prove2me | Theorems.Thm_lean_workbook_plus_22613
-- name    : lean_workbook_plus_22613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/67010845-0c4e-4349-aa22-bac530c7594c
-- statement:
--   For $a, b, c \geq 0$ , with $abc=1$ , prove that \n\n $a+b+c \geq \frac{2}{a+1} + \frac{2}{b+1} + \frac{2}{c+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22613 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a * b * c = 1) : a + b + c ≥ 2 / (a + 1) + 2 / (b + 1) + 2 / (c + 1)   :=  by sorry
