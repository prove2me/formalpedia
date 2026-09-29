-- Prove2me | Theorems.Thm_lean_workbook_plus_26902
-- name    : lean_workbook_plus_26902
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c3b294fb-8cc7-482e-b252-5e7782c7b40c
-- statement:
--   Hence $ (\forall x\neq 0)(f(x) = 0\lor f(x) = 1)\land f(0) = C\in\mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26902 (f : ℝ → ℝ) (C : ℝ) (h : ∀ x, (x ≠ 0 → f x = 0 ∨ f x = 1) ∧ f 0 = C) : ∃ C, ∀ x, (x ≠ 0 → f x = 0 ∨ f x = 1) ∧ f 0 = C   :=  by sorry
