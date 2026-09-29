-- Prove2me | Theorems.Thm_lean_workbook_plus_47096
-- name    : lean_workbook_plus_47096
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/772b9093-b9cd-48fa-93ea-8c40b9d65bf9
-- statement:
--   $\boxed{\text{S1 : }f(x)=-x^2\quad\forall x\in\mathbb Z}$ , which indeed fits .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47096 : ∃ f : ℤ → ℤ, ∀ x, f x = - x^2   :=  by sorry
