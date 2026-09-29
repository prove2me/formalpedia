-- Prove2me | Theorems.Thm_lean_workbook_plus_63762
-- name    : lean_workbook_plus_63762
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5e54627c-cb84-4514-9bfa-d9193c2f367f
-- statement:
--   Prove $\sum_{k=1}^{n} \frac{k^3 + k^2 + 1}{k(k+1)} = \sum_{k=1}^{n} (k+(\frac{1}{k} - \frac{1}{k+1}))$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63762 : ∀ n : ℕ, ∑ k in Finset.Icc 1 n, (k^3 + k^2 + 1) / (k * (k + 1)) = ∑ k in Finset.Icc 1 n, (k + (1 / k - 1 / (k + 1)))   :=  by sorry
