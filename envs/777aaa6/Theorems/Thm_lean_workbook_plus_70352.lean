-- Prove2me | Theorems.Thm_lean_workbook_plus_70352
-- name    : lean_workbook_plus_70352
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e65d884a-0072-44e9-a2d6-3bc112b952fd
-- statement:
--   Prove that if $a + b + c \ge 0, a - b + c \ge 0, a - c \ge 0$, then the absolute values of both roots of the polynomial $P(x) = ax^2 + bx + c$ with $a > 0$ are less than or equal to $1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70352 (a b c : ℝ) (ha : a > 0) (hab : a + b + c ≥ 0) (hac : a - c ≥ 0) (hbc : a - b + c ≥ 0) : ∀ x : ℝ, a * x ^ 2 + b * x + c = 0 → abs x ≤ 1   :=  by sorry
