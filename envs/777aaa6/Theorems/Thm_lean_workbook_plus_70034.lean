-- Prove2me | Theorems.Thm_lean_workbook_plus_70034
-- name    : lean_workbook_plus_70034
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/08e2f8e2-e4a4-4a35-ab98-8dbbdd10e432
-- statement:
--   Prove the identity\n\n$ 1 + \frac{1}{2} - \frac{2}{3} + \frac{1}{4} + \frac{1}{5} - \frac{2}{6} + \ldots + \frac{1}{478} + \frac{1}{479} - \frac{2}{480} = 2 \cdot \sum^{159}_{k=0} \frac{641}{(161+k) \cdot (480-k)}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70034 : 1 + 1 / 2 - 2 / 3 + 1 / 4 + 1 / 5 - 2 / 6 + 1 / 478 + 1 / 479 - 2 / 480 = 2 * ∑ k in Finset.range 159, (641:ℝ) / ((161 + k) * (480 - k))   :=  by sorry
