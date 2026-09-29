-- Prove2me | Theorems.Thm_lean_workbook_plus_58937
-- name    : lean_workbook_plus_58937
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/16627d10-a9f7-4287-b5c5-edc474296ee1
-- statement:
--   Let $Q_n = 1 + \frac14 + \frac19 + \cdots + \frac1{n^2}$ . Then prove that for $n\geq3$ we have: $\frac{19}{12} - \frac1{n+1} < Q_n < \frac74 - \frac1n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58937 (n : ℕ) (hn : 3 ≤ n) : (19 / 12 - 1 / (n + 1) < ∑ i in Finset.range n, (1 / (i + 1)^2) ∧ ∑ i in Finset.range n, (1 / (i + 1)^2) < 7 / 4 - 1 / n)   :=  by sorry
