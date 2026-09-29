-- Prove2me | Theorems.Thm_lean_workbook_plus_15851
-- name    : lean_workbook_plus_15851
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/99850c54-fd17-4196-92b7-e683d02e74bd
-- statement:
--   Given $f(f(x))=x$ for all $x$ and $(x+f(y))(f(x)+y)=xf(x)+yf(y)+2yf(x)$, find $f(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15851 (f : ℝ → ℝ) (hf1 : ∀ x, f (f x) = x) (hf2 : ∀ x y, (x + f y) * (f x + y) = x * f x + y * f y + 2 * y * f x) : ∃ h :ℝ, ∀ x, f x = h * x   :=  by sorry
