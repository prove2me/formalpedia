-- Prove2me | Theorems.Thm_lean_workbook_plus_48196
-- name    : lean_workbook_plus_48196
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ed2f7efb-ccb6-4bd0-b41a-6a8fb246144b
-- statement:
--   Let $a_n=\frac{\sqrt{n-1}}{n}$ $(n\in N^+).$ Then $$a_2+a_3+\cdots+a_n<\frac{2^{n+1}}{2^n+1}\sqrt{n}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48196 : ∀ n : ℕ, (∑ k in Finset.Icc 2 n, (Real.sqrt (k - 1) / k)) < (2 ^ (n + 1) / (2 ^ n + 1)) * Real.sqrt n   :=  by sorry
