-- Prove2me | Theorems.Thm_lean_workbook_plus_33945
-- name    : lean_workbook_plus_33945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/b2fa0a59-a85d-43b4-a2a3-683cb77dee09
-- statement:
--   (a) $f(x)=\begin{cases}x-2 & x\leqslant -{1\over 2}\ 5x & x\geqslant -{1\over 2}\end{cases}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33945 (f : ℝ → ℝ) (x : ℝ) (f_of_le : x ≤ -1 / 2 → f x = x - 2) (f_of_ge : -1 / 2 ≤ x → f x = 5 * x) : f x = if x ≤ -1 / 2 then x - 2 else 5 * x   :=  by sorry
