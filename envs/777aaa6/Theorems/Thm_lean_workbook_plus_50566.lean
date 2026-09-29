-- Prove2me | Theorems.Thm_lean_workbook_plus_50566
-- name    : lean_workbook_plus_50566
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/81367cf1-e214-4c16-a818-9523fe14c46b
-- statement:
--   For $ n\geq 2$ , if $ a,\ b$ satisfy $ a^2 + b^2 = 2^n$ , then prove that both $ a$ and $ b$ are even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50566 (n a b : ℕ) (ha : a^2 + b^2 = 2^n) (hb : 2 ≤ n) : Even a ∧ Even b   :=  by sorry
