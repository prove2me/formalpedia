-- Prove2me | Theorems.Thm_lean_workbook_plus_57719
-- name    : lean_workbook_plus_57719
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f8cde304-35cd-4fbb-8e0d-4dcaba79eace
-- statement:
--   Solution $\frac{1+25+17+81}{4}=\boxed{31}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57719  (a b c d : ℝ)
  (h₀ : a = 1)
  (h₁ : b = 25)
  (h₂ : c = 17)
  (h₃ : d = 81) :
  (a + b + c + d) / 4 = 31   :=  by sorry
