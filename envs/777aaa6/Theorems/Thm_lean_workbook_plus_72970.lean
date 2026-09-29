-- Prove2me | Theorems.Thm_lean_workbook_plus_72970
-- name    : lean_workbook_plus_72970
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/55c9c7bd-24c9-40b8-aba3-064e3efc7677
-- statement:
--   f is odd $f(x^2 + 2x) = f(x)(f(x)+2)$ and $f(x^2 + 2x) = f(-x)(f(-x)-2)$ imply $f(-x)=-f(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72970 (f : ℤ → ℤ) (h₁ : ∀ x, f (x^2 + 2*x) = f x * (f x + 2)) (h₂ : ∀ x, f (x^2 + 2*x) = f (-x) * (f (-x) - 2)) : ∀ x, f (-x) = - f x   :=  by sorry
