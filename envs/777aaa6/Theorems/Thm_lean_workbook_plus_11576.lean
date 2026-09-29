-- Prove2me | Theorems.Thm_lean_workbook_plus_11576
-- name    : lean_workbook_plus_11576
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2aa0175d-75a7-4e91-89f4-d684c8c09201
-- statement:
--   Find all functions $f:\mathbb R\rightarrow\mathbb R$ such that for all $x,y\in\mathbb R$ ,\n\n$(x+y)(f(x)-f(y)) = (x-y)(f(x)+f(y))$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11576 (f : ℝ → ℝ):(∀ x y, (x + y) * (f x - f y) = (x - y) * (f x + f y)) ↔ ∃ a:ℝ, ∀ x, f x = a * x   :=  by sorry
