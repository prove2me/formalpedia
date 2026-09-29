-- Prove2me | Theorems.Thm_lean_workbook_plus_13276
-- name    : lean_workbook_plus_13276
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/da86fb87-29fb-48cd-aca1-7aa95bf33486
-- statement:
--   Prove that $\frac{1}{{S_1^2}} + \frac{1}{{2S_2^2}} + \frac{1}{{3S_3^2}} + ...\frac{1}{{nS_n^2}} < 2$ where ${S_n} = 1 + \frac{1}{2} + \frac{1}{3} + ... + \frac{1}{n}$ and $n \in \mathbb{N}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13276 : ∀ n : ℕ, (∑ k in Finset.Icc 1 n, (1 : ℝ) / (k * (∑ m in Finset.Icc 1 k, 1 / m) ^ 2)) < 2   :=  by sorry
