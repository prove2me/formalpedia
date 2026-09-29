-- Prove2me | Theorems.Thm_lean_workbook_plus_70664
-- name    : lean_workbook_plus_70664
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/de5b513a-9466-4dc1-bcfe-bcadbecb3a8e
-- statement:
--   Determine the convergence of $\sum_{n=2}^{infty} \frac{log(n)}{n(n-1)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70664 : ∀ n : ℕ, n ≥ 2 → 0 ≤ ‖(Real.log n) / (n * (n - 1))‖   :=  by sorry
