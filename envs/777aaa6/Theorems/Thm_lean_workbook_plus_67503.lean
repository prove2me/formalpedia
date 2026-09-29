-- Prove2me | Theorems.Thm_lean_workbook_plus_67503
-- name    : lean_workbook_plus_67503
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/6056f77c-b860-4d25-8bff-563efd811fa1
-- statement:
--   By AM-HM: $ \frac{a+b}{2} \geq \frac{2}{\frac{1}{a}+\frac{1}{b}} \implies a+b \geq \frac{4}{\frac{1}{a}+\frac{1}{b}} = \frac{1}{\frac{1}{4a}+\frac{1}{4b}} \implies \frac{1}{4a}+\frac{1}{4b} \geq \frac{1}{a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67503  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b) :
  1 / (4 * a) + 1 / (4 * b) ≥ 1 / (a + b)   :=  by sorry
