-- Prove2me | Theorems.Thm_lean_workbook_plus_77641
-- name    : lean_workbook_plus_77641
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a6a6b79f-4ee3-45ed-9e3b-c5b00143e152
-- statement:
--   $s_{n+1}-s_n=\sum_1^{n+1} {{(-1)^{k+1}}\over k}{{n+1}\choose k}-\sum_1^n {{(-1)^{k+1}}\over k}{n\choose k}={{(-1)^{n+2}}\over {n+1}}+\sum_1^n {{(-1)^{k+1}}\over k}{n\choose {k-1}}=\{{(-1)^{n+2}}\over {n+1}}+{1\over {n+1}}\sum_1^n (-1)^{k+1}{{n+1}\choose k}={1\over {n+1}}\sum_1^{n+1} (-1)^{k+1}{{n+1}\choose k}={1\over {n+1}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77641 : ∀ n : ℕ, ((n + 1).choose (n + 1) - ∑ k in Finset.range (n + 1), ((-1 : ℤ)^(k + 1) / (k + 1) * (n + 1).choose k)) = 1 / (n + 1)   :=  by sorry
