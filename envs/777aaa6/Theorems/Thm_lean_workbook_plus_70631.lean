-- Prove2me | Theorems.Thm_lean_workbook_plus_70631
-- name    : lean_workbook_plus_70631
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2a5fed35-9abf-4b2e-93f0-859a48215d32
-- statement:
--   Prove that $x^2 - yx \leq 1 - y$ for $1 \leq x \leq y - 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70631 (x y : ℝ) (h₁ : 1 ≤ x ∧ x ≤ y - 1) (h₂ : 1 ≤ y) : x^2 - y * x ≤ 1 - y   :=  by sorry
