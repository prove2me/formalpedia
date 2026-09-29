-- Prove2me | Theorems.Thm_lean_workbook_plus_69605
-- name    : lean_workbook_plus_69605
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/89d0d3c6-0d14-49e9-94ca-02a744b8fd42
-- statement:
--   Prove that $\sum_{i=1}^{n}{i^2}=\frac{n(n+1)(2n+1)} {6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69605 : ∀ n : ℕ, ∑ i in Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry
