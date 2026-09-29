-- Prove2me | Theorems.Thm_lean_workbook_plus_10699
-- name    : lean_workbook_plus_10699
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/01359281-6e85-4c49-8baf-14e1727583a7
-- statement:
--   $\left ( \frac{1}{2} \right )^n \frac{n+2}{n(n+1)} = \frac{1}{2^{n-1} n} - \frac{1}{2^n (n+1)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10699 ∀ n : ℕ, (1 / 2)^n * ((n + 2) / (n * (n + 1))) = 1 / (2^(n - 1) * n) - 1 / (2^n * (n + 1))   :=  by sorry
