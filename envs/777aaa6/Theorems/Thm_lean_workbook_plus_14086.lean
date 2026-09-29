-- Prove2me | Theorems.Thm_lean_workbook_plus_14086
-- name    : lean_workbook_plus_14086
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9c5d3d2d-56be-40ef-bb35-2ef1bb7fc811
-- statement:
--   Show that there does not exist a non constant continuous $f : \mathbb{R}^2 \mapsto \mathbb{R}$ such that $f(x,y)=5~~\forall~~(x,y) \in \mathbb{R}^2 $ with $x^2+y^2<1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14086 : ¬∃ f : ℝ × ℝ → ℝ, (∀ x : ℝ × ℝ, x.fst ^ 2 + x.snd ^ 2 < 1 → f x = 5) ∧ ¬∀ x y : ℝ × ℝ, f x = f y   :=  by sorry
