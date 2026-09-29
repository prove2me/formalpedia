-- Prove2me | Theorems.Thm_lean_workbook_plus_38012
-- name    : lean_workbook_plus_38012
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/35e78c5b-d84f-4812-a0f4-8614f0e5e14d
-- statement:
--   What theorems are used in the implication $x \geq 0$ and $y \geq 0 \Longrightarrow (\sqrt{x})^2 = x$ and $(\sqrt{y})^2 = y$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38012  (x y : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : 0 ≤ y) :
  Real.sqrt x ^ 2 = x ∧ Real.sqrt y ^ 2 = y   :=  by sorry
