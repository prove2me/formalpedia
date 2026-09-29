-- Prove2me | Theorems.Thm_lean_workbook_plus_42153
-- name    : lean_workbook_plus_42153
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/459b0183-7ccf-4a36-a05c-9bd6892cec14
-- statement:
--   Prove that $ \sum_{r = 1}^{n} \frac{r}{(r+1)(r+2)(r+3)} = \frac{1}{4} + \frac{1}{2}\left(\frac{1}{n+2} - \frac{3}{n+3}\right) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42153 (n : ℕ) : ∑ r in Finset.Icc 1 n, r / (r + 1) / (r + 2) / (r + 3) = 1 / 4 + 1 / 2 * (1 / (n + 2) - 3 / (n + 3))   :=  by sorry
