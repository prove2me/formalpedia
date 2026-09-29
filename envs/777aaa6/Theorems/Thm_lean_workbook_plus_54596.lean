-- Prove2me | Theorems.Thm_lean_workbook_plus_54596
-- name    : lean_workbook_plus_54596
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/8c565774-f9ea-4e15-a108-1b4792b794e2
-- statement:
--   Prove that:\n\n$ 1+\frac{1}{\sqrt{2}}+\frac{1}{\sqrt{3}}+...+\frac{1}{\sqrt{n}}\geqslant \sqrt{n}$\n\n$n$ is natural number
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54596 : ∀ n : ℕ, (∑ k in Finset.range n, (1 / Real.sqrt k)) ≥ Real.sqrt n   :=  by sorry
