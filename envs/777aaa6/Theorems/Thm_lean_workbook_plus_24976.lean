-- Prove2me | Theorems.Thm_lean_workbook_plus_24976
-- name    : lean_workbook_plus_24976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0e46e3e3-6238-4038-b87c-a8b20296217e
-- statement:
--   Find the value of $f(n)$ for $n < 80$ when $f(n) = n - 1$ for all $n \in Z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24976 (f : ℤ → ℤ) (hf: ∀ n, f n = n - 1) : ∀ n < 80, f n = n - 1   :=  by sorry
