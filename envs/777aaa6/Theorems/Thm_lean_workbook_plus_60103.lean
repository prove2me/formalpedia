-- Prove2me | Theorems.Thm_lean_workbook_plus_60103
-- name    : lean_workbook_plus_60103
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/96f5b702-9fbe-4f70-8d10-ce662214280c
-- statement:
--   Let be $ a,b\in \mathbb{R}$ and let be $ f: \mathbb{R}\rightarrow \mathbb{R}$ such that $ a\cdot f(x)+b\cdot f(1-x)=x\ (1)\ ,\ (\forall)x\in \mathbb{R}$ .\n\ni)Show that $ f(x)+f(1-x)=\frac{1}{a+b}\ ,\ (\forall)x\in \mathbb{R}\ ,\ a\neq -b$ ;\n\nii)If $ a=b$ , prove that $ (\nexists)f$ satisfying $ (1)$ ;\n\nii)If $ a\neq b$ , find $ f$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60103 (a b : ℝ) (f : ℝ → ℝ) (h₁ : a ≠ -b) (h₂ : ∀ x, a * f x + b * f (1 - x) = x) : ∀ x, f x + f (1 - x) = 1 / (a + b)   :=  by sorry
