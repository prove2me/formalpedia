-- Prove2me | Theorems.Thm_lean_workbook_plus_13094
-- name    : lean_workbook_plus_13094
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5ea8a396-7b91-4119-8ea9-531ca2d84cf9
-- statement:
--   Find all functions $f:\mathbb{R}\to\mathbb{R}$ such that $(x+y)(f(x)-f(y))=f(x^2)-f(y^2)$ for all $x,y\in\mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13094 (f : ℝ → ℝ):(∀ x y, (x + y) * (f x - f y) = f (x ^ 2) - f (y ^ 2)) ↔ ∃ a b:ℝ, ∀ x, f x = a * x + b   :=  by sorry
