-- Prove2me | Theorems.Thm_lean_workbook_plus_13244
-- name    : lean_workbook_plus_13244
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/626a1331-ab6c-48c9-89ad-b792dc63fd2d
-- statement:
--   a) $ \sum_{i=0}^n \frac{1}{1+i}\binom{n}{i}=\frac{1}{n+1}\{2^{n+1}-1\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13244 : ∀ n : ℕ, ∑ i in Finset.range (n+1), (1/(1+i)) * (n.choose i) = (1/(n+1)) * (2^(n+1) - 1)   :=  by sorry
