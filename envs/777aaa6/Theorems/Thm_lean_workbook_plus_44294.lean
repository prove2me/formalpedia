-- Prove2me | Theorems.Thm_lean_workbook_plus_44294
-- name    : lean_workbook_plus_44294
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e47bcdbd-b503-4b09-8d7f-ce0310fb9987
-- statement:
--   Find all functions $f:\mathbb R\rightarrow\mathbb R$ such that for all $x,y\in\mathbb R$ ,\n\n$(x+y)(f(x)-f(y)) = (x-y)(f(x)+f(y))$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44294 (f : ℝ → ℝ): (∀ x y : ℝ, (x + y) * (f x - f y) = (x - y) * (f x + f y)) ↔ ∃ a:ℝ, ∀ x : ℝ, f x = a * x   :=  by sorry
