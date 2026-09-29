-- Prove2me | Theorems.Thm_lean_workbook_plus_27610
-- name    : lean_workbook_plus_27610
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/86fbf8a2-d84f-4b4b-946f-653ec282310f
-- statement:
--   Prove by induction that $\sum_{k=1}^n\frac{k}{(k+1)!} = 1- \frac{1}{(n+1)!}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27610 : ∀ n : ℕ, ∑ k in Finset.Icc 1 n, k / (k + 1)! = 1 - 1 / (n + 1)!   :=  by sorry
