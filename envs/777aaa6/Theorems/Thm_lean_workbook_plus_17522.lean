-- Prove2me | Theorems.Thm_lean_workbook_plus_17522
-- name    : lean_workbook_plus_17522
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a6993e43-31da-45d5-a821-27945b61f7e8
-- statement:
--   What if the function $g(a)$ was defined as $g(a) = 0$ for all $a$ in the interval $[0, 1]$? Show that $g$ is continuous on that interval, but there is no $a \in [0, 1]$ such that $g(a) = \frac{1}{a} + \frac{1}{1-a}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17522 (g : ℝ → ℝ) (hg : ∀ x ∈ Set.Icc (0:ℝ) 1, g x = 0) : ContinuousOn g (Set.Icc (0:ℝ) 1)   :=  by sorry
