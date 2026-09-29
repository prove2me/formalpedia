-- Prove2me | Theorems.Thm_lean_workbook_plus_61629
-- name    : lean_workbook_plus_61629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/bed0b7d7-2180-4158-a626-d1bbadc7e42b
-- statement:
--   Equality occurs when $ a=b=\frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61629  (a b : ℝ)
  (h₀ : a * b = 9 / 4)
  (h₁ : a + b = 3) :
  a = 3 / 2 ∧ b = 3 / 2   :=  by sorry
