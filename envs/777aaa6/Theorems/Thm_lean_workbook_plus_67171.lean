-- Prove2me | Theorems.Thm_lean_workbook_plus_67171
-- name    : lean_workbook_plus_67171
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/1a623df0-6ae6-40a3-b263-bf0e91bdca83
-- statement:
--   Find all functions if $f:\mathbb{R}\to\mathbb{R}$ for $\forall x,y\in\mathbb{R}$ then $(x+y)(f(x)-f(y))=f(x^2)-f(y^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67171 (f : ℝ → ℝ):(∀ x y :ℝ, (x+y)*(f x - f y) = f (x^2) - f (y^2)) ↔ ∃ a b :ℝ, ∀ x : ℝ, f x = a * x + b   :=  by sorry
