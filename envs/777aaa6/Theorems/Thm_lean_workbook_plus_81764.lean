-- Prove2me | Theorems.Thm_lean_workbook_plus_81764
-- name    : lean_workbook_plus_81764
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/bea9506f-e567-4e8b-8b06-b79059ca673c
-- statement:
--   A sequence ${ a_n }$ is defined as follows: \n $a_1 = 1$ \nFor $n\geq 1$ , \n $a_{n+1} = \frac{a_n}{1+n\cdot a_n}$ . \nFind an explicit formula for $a_n$ , if exists. Hence, find the value of $a_{2012}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81764 (a : ℕ → ℝ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = a n / (1 + n * a n)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
