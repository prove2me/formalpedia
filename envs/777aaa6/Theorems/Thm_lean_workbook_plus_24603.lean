-- Prove2me | Theorems.Thm_lean_workbook_plus_24603
-- name    : lean_workbook_plus_24603
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/5cb967df-89ed-488b-a947-39f04e092b0c
-- statement:
--   Prove that $\frac{1}{n^{2}+n+1}=\frac{\left(n+1\right)-n}{1+n\left(n+1\right)}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24603 : ∀ n : ℕ, 1 / (n ^ 2 + n + 1) = (n + 1 - n) / (1 + n * (n + 1))   :=  by sorry
