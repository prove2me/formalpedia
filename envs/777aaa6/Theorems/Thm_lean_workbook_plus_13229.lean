-- Prove2me | Theorems.Thm_lean_workbook_plus_13229
-- name    : lean_workbook_plus_13229
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/233296f2-e1f8-4cdc-9c31-52b3377797a6
-- statement:
--   So, what we have to show is that $ \sum_{k = 1}^{n^2 - 1}\sqrt k \leq \frac {n^2 - 1}2 + \frac {4n^3 - 3n^2 - n}6 \iff \sum_{k = 1}^{n^2 - 1}\sqrt k \leq \frac {4n^3 - n - 3}6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13229 : ∀ n, ∑ k in Finset.range (n^2 - 1), Real.sqrt k ≤ (n^2 - 1) / 2 + (4 * n^3 - 3 * n^2 - n) / 6   :=  by sorry
