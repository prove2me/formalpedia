-- Prove2me | Theorems.Thm_lean_workbook_plus_78363
-- name    : lean_workbook_plus_78363
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/2825b746-98f1-4436-97c0-4ba73413483f
-- statement:
--   Let $a_1,a_2,...,a_n$ be real numbers. Prove that $\sqrt[3]{a_1^3+a_2^3+...+a_n^3}\leq \sqrt{a_1^2+a_2^2+...+a_n^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78363 (n : ℕ) (a : ℕ → ℝ) : (∑ i in Finset.range n, (a i) ^ 3) ^ (1 / 3) ≤ (∑ i in Finset.range n, (a i) ^ 2) ^ (1 / 2)   :=  by sorry
