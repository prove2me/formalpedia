-- Prove2me | Theorems.Thm_lean_workbook_plus_80081
-- name    : lean_workbook_plus_80081
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c6a88a40-eba5-4f82-8534-f58d5a6b99cb
-- statement:
--   Determine the convergence of the series $\sum_{k=1}^{\infty} \frac{\ln(k)}{k^2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80081 : ∀ k : ℕ, (0 : ℝ) ≤ |(Real.log k)/k^2|   :=  by sorry
