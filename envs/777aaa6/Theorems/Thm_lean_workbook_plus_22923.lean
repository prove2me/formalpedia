-- Prove2me | Theorems.Thm_lean_workbook_plus_22923
-- name    : lean_workbook_plus_22923
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/65db80f8-36ef-4b56-bc58-42f4a027e6d1
-- statement:
--   Determine the convergence or divergence of the series: $\sum_{n=1}^{\infty}\frac{\sin n^2}{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22923 : ∃ l, ∑' n : ℕ, (sin n^2 / n) = l   :=  by sorry
