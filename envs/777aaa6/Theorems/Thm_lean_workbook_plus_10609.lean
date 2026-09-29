-- Prove2me | Theorems.Thm_lean_workbook_plus_10609
-- name    : lean_workbook_plus_10609
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8f8c44ef-0f26-440e-99f2-bc9702f4c74e
-- statement:
--   By Cauchy $b^{2}+c^{2}\ge 2bc $ . $ f\ge 2(b^{2}c^{2}+a^{2}b^{2}+a^{2}c^{2}-abc(a+b+c)=2(a(b-c)^{2}+b(a-c)^{2}+c(a-b)^{2})\geq 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10609  (a b c : ℝ)
  (f : ℝ)
  (h₀ : f = 2 * (b^2 * c^2 + a^2 * b^2 + a^2 * c^2 - a * b * c * (a + b + c)))
  (h₁ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₂ : a + b > c)
  (h₃ : a + c > b)
  (h₄ : b + c > a) :
  f ≥ 0   :=  by sorry
