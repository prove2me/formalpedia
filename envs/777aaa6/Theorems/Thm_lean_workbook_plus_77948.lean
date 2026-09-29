-- Prove2me | Theorems.Thm_lean_workbook_plus_77948
-- name    : lean_workbook_plus_77948
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/5d6afac6-d594-417f-98fe-dd1db7bca43d
-- statement:
--   What about the function $ f(x,y)=\begin{cases}y&-x\le y\le x\\-y&x\le y\le -x\\x&-y\le x\le y\\-x&y\le x\le -y\end{cases}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77948 (x y : ℝ) (f : ℝ × ℝ → ℝ) (hf: f (x,y) = if (-x) ≤ y ∧ y ≤ x then y else if x ≤ y ∧ y ≤ (-x) then (-y) else if (-y) ≤ x ∧ x ≤ y then x else (-y)) : |f (x,y)| ≤ |x| + |y|   :=  by sorry
