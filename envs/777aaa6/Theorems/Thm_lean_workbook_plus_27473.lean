-- Prove2me | Theorems.Thm_lean_workbook_plus_27473
-- name    : lean_workbook_plus_27473
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/05ecd5a8-002d-4657-bf95-414c31c887d3
-- statement:
--   Either $y=s-940+\frac 12+\sqrt{s-940+\frac 14}$ and $s\ge 940-\frac 14$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27473  (y s : ℝ)
  (h₀ : 0 < s - 940 + 1 / 4)
  (h₁ : 0 < s - 940 + 1 / 2)
  (h₂ : 0 < s - 940 + 1)
  (h₃ : s - 940 + 1 / 4 ≤ s)
  (h₄ : s - 940 + 1 / 2 ≤ s)
  (h₅ : s - 940 + 1 ≤ s)
  (h₆ : y = s - 940 + 1 / 2 + Real.sqrt (s - 940 + 1 / 4)) :
  y = s - 940 + 1 / 2 + Real.sqrt (s - 940 + 1 / 4) ∧ s ≥ 940 - 1 / 4   :=  by sorry
