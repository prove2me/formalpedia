-- Prove2me | Theorems.Thm_lean_workbook_plus_41825
-- name    : lean_workbook_plus_41825
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/408c453d-9220-454b-b939-bb4f2078d58c
-- statement:
--   A consequence of this result is that $(1-\frac {1}{2})(1-\frac{1}{2^3})....(1-\frac{1}{2^{2n-1}})>\frac{2}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41825 : ∀ n : ℕ, (∏ i in Finset.range n, (1 - (1:ℝ) / 2^(2 * i - 1))) > 2 / 5   :=  by sorry
