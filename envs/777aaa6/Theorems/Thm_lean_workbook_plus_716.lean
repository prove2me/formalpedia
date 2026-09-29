-- Prove2me | Theorems.Thm_lean_workbook_plus_716
-- name    : lean_workbook_plus_716
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0b4cf1e9-4017-4f7e-b536-2fff68ad87ee
-- statement:
--   Find all functions $f(x)$ defined on integers with integer values such that $f(2013) = 2014$ and for each integer $n$, if $f(n) = m$ then $f(m) = n$ and $f(m + 3) = n - 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_716 (f : ℤ → ℤ) (h₁ : f 2013 = 2014) (h₂ : ∀ n, f n = m → f m = n ∧ f (m + 3) = n - 3) : ∀ n, f n = n + 1   :=  by sorry
