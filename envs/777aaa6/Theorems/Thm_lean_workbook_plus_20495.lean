-- Prove2me | Theorems.Thm_lean_workbook_plus_20495
-- name    : lean_workbook_plus_20495
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/41126dee-b866-4005-8c55-9aa7cda533ee
-- statement:
--   Notice that on the interval $\left[i-\frac{1}{2},\,i + \frac{1}{2}\right]$, $i = 1,\,2,...,\,n$ we have $f(x) = |x - i|$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20495 (n : ℕ) (f : ℝ → ℝ) (hf: f = fun x ↦ abs (x - ↑i)) : ∀ x ∈ Set.Icc (i - 1 / 2) (i + 1 / 2), f x = abs (x - i)   :=  by sorry
