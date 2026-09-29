-- Prove2me | Theorems.Thm_lean_workbook_plus_73872
-- name    : lean_workbook_plus_73872
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/46614824-0444-42e3-b773-ad82d03a2a1b
-- statement:
--   We can assume that our variables are non-negatives because $\sqrt[3]{a_1^3+a_2^3+...+a_n^3}\leq\sqrt[3]{|a_1|^3+|a_2|^3+...+|a_n|^3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73872 (n : ℕ) (a : ℕ → ℝ) : (∑ i in Finset.range n, (a i) ^ 3) ^ (1 / 3) ≤ (∑ i in Finset.range n, |(a i)| ^ 3) ^ (1 / 3)   :=  by sorry
