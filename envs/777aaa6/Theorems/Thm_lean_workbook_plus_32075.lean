-- Prove2me | Theorems.Thm_lean_workbook_plus_32075
-- name    : lean_workbook_plus_32075
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/87d3fa87-d6c5-4f20-96b6-3269de48bb1d
-- statement:
--   Wlog, let $x\ge y$ Now by chebyshev, $(x^3+y^3)\ge \frac{(x^2+y^2)(x+y)}{2}\ge \frac{(x+y)^3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32075  (x y : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y)
  (h₁ : x ≥ y) :
  x^3 + y^3 ≥ (x^2 + y^2) * (x + y) / 2 ∧ (x^2 + y^2) * (x + y) / 2 ≥ (x + y)^3 / 4   :=  by sorry
