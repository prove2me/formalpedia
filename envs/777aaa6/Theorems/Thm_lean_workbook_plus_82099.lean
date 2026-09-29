-- Prove2me | Theorems.Thm_lean_workbook_plus_82099
-- name    : lean_workbook_plus_82099
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2d03f866-0b65-4a37-97d2-39da12f715d2
-- statement:
--   Prove by induction that $\sum_{n=1}^{k}\frac{n}{(n+1)!}=1-\frac{1}{(k+1)!}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82099 : ∀ k : ℕ, (∑ n in Finset.Icc 1 k, n / (n + 1)!) = 1 - 1 / (k + 1)!   :=  by sorry
