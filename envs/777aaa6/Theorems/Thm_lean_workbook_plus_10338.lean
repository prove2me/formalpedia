-- Prove2me | Theorems.Thm_lean_workbook_plus_10338
-- name    : lean_workbook_plus_10338
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/b54c0d18-52a7-4d59-acc7-74f42e4035ce
-- statement:
--   By AM-GM, $\frac{1}{a_1}+\frac{1}{a_2}+\cdots+\frac{1}{a_n}=1\implies 1\geq \frac{n}{\sqrt[n]{a_1a_2\cdots a_n}}\Longleftrightarrow a_1a_2\cdots a_n\geq n^n.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10338  ∀ n : ℕ, ∀ a : ℕ → ℕ, (∑ x in Finset.range n, 1 / a x) = 1 → n ^ n ≤ ∏ x in Finset.range n, a x   :=  by sorry
