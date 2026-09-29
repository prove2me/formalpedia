-- Prove2me | Theorems.Thm_lean_workbook_plus_47364
-- name    : lean_workbook_plus_47364
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/aca1d437-6379-4872-9aa8-45d931d16294
-- statement:
--   $\boxed{\text{S1 : }f(x)=k\pi\quad\forall x}$ , which indeed fits, whatever is $k\in\mathbb Z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47364 (x : ℝ) (k : ℤ) : ∃ f : ℝ → ℝ, ∀ x, f x = k * π   :=  by sorry
