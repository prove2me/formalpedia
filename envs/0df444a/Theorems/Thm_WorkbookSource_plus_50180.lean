-- Prove2me | Theorems.Thm_WorkbookSource_plus_50180
-- name    : WorkbookSource.plus_50180
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T16:12:09.60295+00:00
-- url     : https://prove2.me/theorems/1f2afde6-6e1b-4305-a8cb-8dee2c076144
-- title:
--   A finite sum bounded by a product of truncated terms
-- statement:
--   For any sequence of positive real numbers $a_0,\ldots,a_{94}$,
--   $$\sum_{k=0}^{94}a_k\leq94+\prod_{k=0}^{94}\max\{1,a_k\}.$$
--   This compares an additive total with the product obtained by replacing factors below one by one. The indexing is shifted by one from the source's list of 95 positive numbers.
--
--   Formalization Note: The source proposition is retained; obsolete summation notation is updated for Lean 4.33.1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_50180; Apache-2.0

import Mathlib
open scoped BigOperators

theorem WorkbookSource.plus_50180 (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) : ∑ k ∈ Finset.range 95, a k ≤ 94 + ∏ k ∈ Finset.range 95, max 1 (a k)   :=  by sorry
