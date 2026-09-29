-- Prove2me | Theorems.Thm_lean_workbook_plus_21630
-- name    : lean_workbook_plus_21630
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/484ebe1e-039d-49e3-83f0-f1b4ed6af58f
-- statement:
--   Find a closed expression for the limit of the sequence $u_n= \prod_{i=1}^n(1+\frac1{2^i})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21630 : ∃ (u : ℕ → ℝ), ∀ n, u n = ∏ i in Finset.range n, (1 + (1:ℝ) / 2 ^ i)   :=  by sorry
