-- Prove2me | Theorems.Thm_lean_workbook_plus_5773
-- name    : lean_workbook_plus_5773
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4708e64c-9d43-499a-989d-6967f2967b06
-- statement:
--   Prove that $ \prod_{k=2}^{n} {\frac {k^2-1}{k^2}} = \frac {n+1}{2n}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5773 : ∀ n : ℕ, (∏ k in Finset.Icc 2 n, (k^2 - 1)/k^2) = (n + 1)/(2 * n)   :=  by sorry
