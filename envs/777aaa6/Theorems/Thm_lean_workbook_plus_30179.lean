-- Prove2me | Theorems.Thm_lean_workbook_plus_30179
-- name    : lean_workbook_plus_30179
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/71f60263-85ad-46e1-bb39-01a5680a2ef2
-- statement:
--   Find $f$ so that $f:R\rightarrow R$ and : \ncos(f(x+y))=f(x)cos(y)+f(y)cos(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30179 (f : ℝ → ℝ) (hf: ∀ x y : ℝ, (Real.cos (f (x + y))) = f x * Real.cos y + f y * Real.cos x) : ∃ k:ℝ, ∀ x:ℝ, f x = k * x   :=  by sorry
