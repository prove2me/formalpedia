-- Prove2me | Theorems.Thm_lean_workbook_plus_17582
-- name    : lean_workbook_plus_17582
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/69c5701d-3bd9-4f78-8c4b-dce5eb2590fc
-- statement:
--   Determine the convergence of the series: $\sum^{\infty}_{n=2}\frac{((\ln) n)^2}{n^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17582 : ∀ n : ℕ, n ≥ 2 → 0 ≤ ‖((Real.log n)^2)/(n^2)‖   :=  by sorry
