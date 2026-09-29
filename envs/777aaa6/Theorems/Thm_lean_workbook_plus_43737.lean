-- Prove2me | Theorems.Thm_lean_workbook_plus_43737
-- name    : lean_workbook_plus_43737
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cba6985b-ea94-40a7-8b5f-20b5c393b0c2
-- statement:
--   We have $S=1+3+5+\cdots +195+197+199,S=199+197+...+5+3+1$ , so $2S=(199+1)+(197+3)+...+(3+197)+(1+199)=100\cdot 200=20000\Rightarrow S=10000$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43737  (s : ℕ)
  (h₀ : s = ∑ k in Finset.Icc (1 : ℕ) 100, (2 * k - 1)) :
  s = 10000   :=  by sorry
