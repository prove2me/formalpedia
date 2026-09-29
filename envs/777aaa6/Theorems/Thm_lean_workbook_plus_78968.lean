-- Prove2me | Theorems.Thm_lean_workbook_plus_78968
-- name    : lean_workbook_plus_78968
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ad1723d0-6a2f-4861-870c-cffa6b5e70fb
-- statement:
--   ${(1+x)}^{n}= \sum_{k=0}^{n}\binom{n}{k}x^{k}$ and ${(1+\frac{1}{x})}^{n}= \sum_{k=0}^{n}\binom{n}{k}{(\frac{1}{x})}^{k}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78968 : ∀ n : ℕ, (1 + x)^n = ∑ k in Finset.range (n + 1), (n.choose k) * x^k ∧ (1 + 1/x)^n = ∑ k in Finset.range (n + 1), (n.choose k) * (1/x)^k   :=  by sorry
