-- Prove2me | Theorems.Thm_lean_workbook_plus_26308
-- name    : lean_workbook_plus_26308
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c4f201d1-4d25-486c-bb06-c35f7b1d33ca
-- statement:
--   给定 $ y^2\le x\le1$ 和 $ 0\le y\le1$，找出新的积分限制
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26308 (x y : ℝ) (h₁ : y^2 ≤ x ∧ x ≤ 1) (h₂ : 0 ≤ y ∧ y ≤ 1) : 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1   :=  by sorry
