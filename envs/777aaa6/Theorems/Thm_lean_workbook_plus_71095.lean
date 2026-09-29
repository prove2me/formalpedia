-- Prove2me | Theorems.Thm_lean_workbook_plus_71095
-- name    : lean_workbook_plus_71095
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9adf3a7e-f80b-4650-a1b6-71390178e3f0
-- statement:
--   Find the value of $f(100)$ if $f(n) = \frac{n+1}{n-1}$ for all positive integers $n > 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71095 (f : ℕ → ℝ) (hf : ∀ n, 1 < n → f n = (n + 1) / (n - 1)) : f 100 = 101 / 99   :=  by sorry
