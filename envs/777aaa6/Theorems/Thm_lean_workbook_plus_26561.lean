-- Prove2me | Theorems.Thm_lean_workbook_plus_26561
-- name    : lean_workbook_plus_26561
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f40b8c3e-3d39-42e7-85b5-0b0c7dd3ccb8
-- statement:
--   After making the substitution $x=\frac{1}{a}$, $y=\frac{1}{b}$, and $z=\frac{1}{c}$, we have the system: \n$ a+b = \frac{5}{6} $ \n$ b+c = \frac{7}{10} $ \n$ c+a = \frac{8}{15} $ \nFind the values of $a$, $b$, and $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26561 (a b c : ℝ) : a+b = 5/6 ∧ b+c = 7/10 ∧ c+a = 8/15 ↔ a = 1/3 ∧ b = 1/2 ∧ c = 1/5   :=  by sorry
