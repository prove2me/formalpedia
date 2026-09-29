-- Prove2me | Theorems.Thm_lean_workbook_plus_5584
-- name    : lean_workbook_plus_5584
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/24b8df9b-8243-438e-b475-10ba3465e554
-- statement:
--   Observe that $\sum_{n=1}^{\infty}(-1)^{n}\frac{e^{2n}}{(2n)!}<\infty$ , in other words the series converges.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5584 : ∃ y, y = ∑' n : ℕ, (-1 : ℝ)^n * (exp 2)^n / (2 * n)!   :=  by sorry
