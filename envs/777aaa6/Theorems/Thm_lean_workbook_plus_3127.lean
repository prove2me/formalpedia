-- Prove2me | Theorems.Thm_lean_workbook_plus_3127
-- name    : lean_workbook_plus_3127
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e2db9350-ca53-4871-a72b-e91afa89b3b7
-- statement:
--   We have this: $\frac{2+{{x}^{2}}+{{y}^{2}}}{1+{{x}^{2}}+{{y}^{2}}+{{x}^{2}}{{y}^{2}}}\ge \frac{2}{1+xy}\Rightarrow (2xy-1)(xy-1)\le 0\Leftrightarrow xy\in \left[ \frac{1}{2},1 \right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3127  (x y : ℝ)
  (h₀ : 0 ≤ 1 + x^2 + y^2 + x^2 * y^2)
  (h₁ : 0 ≤ 2 + x^2 + y^2)
  (h₂ : 1 + x^2 + y^2 + x^2 * y^2 ≠ 0)
  (h₃ : 2 + x^2 + y^2 ≠ 0)
  (h₄ : 0 ≤ x * y) :
  (2 * x * y - 1) * (x * y - 1) ≤ 0 ↔ x * y ∈ Set.Icc (1 / 2) 1   :=  by sorry
