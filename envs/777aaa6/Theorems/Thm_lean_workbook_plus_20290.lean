-- Prove2me | Theorems.Thm_lean_workbook_plus_20290
-- name    : lean_workbook_plus_20290
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4bdd98bf-3533-4d88-9042-c40f81db7e7b
-- statement:
--   Step 3 : For all $x \leq x_{1}$ : $y(x) \leq z(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20290 (x₁ : ℝ) (y z : ℝ → ℝ) (h₁ : ∀ x, x ≤ x₁ → y x ≤ z x) : ∀ x, x ≤ x₁ → y x ≤ z x   :=  by sorry
