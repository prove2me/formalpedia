-- Prove2me | Theorems.Thm_lean_workbook_plus_27314
-- name    : lean_workbook_plus_27314
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6f3f8d19-00dd-4707-b232-15747aac2f75
-- statement:
--   Let $P(x,y)$ be the assertion $f(xf(y)+yf(x))=x^2+y^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27314 (f : ℝ → ℝ) (hf : ∀ x y, f (x * f y + y * f x) = x ^ 2 + y ^ 2) : ∃ k, ∀ x, f x = k * x ∨ ∀ x, f x = k / x   :=  by sorry
