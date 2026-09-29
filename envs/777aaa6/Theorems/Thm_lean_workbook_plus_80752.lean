-- Prove2me | Theorems.Thm_lean_workbook_plus_80752
-- name    : lean_workbook_plus_80752
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/76cadff1-5ea8-4db6-a3df-c42e50d18e2b
-- statement:
--   Note that $F_n=\frac 1{\sqrt 5}\left(\left(\frac {1+\sqrt 5}2\right)^n-\left(\frac{1-\sqrt 5}2\right)^n\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80752 : ∀ n : ℕ, fib n = (1 / Real.sqrt 5) * ((1 + Real.sqrt 5) / 2)^n - ((1 - Real.sqrt 5) / 2)^n   :=  by sorry
