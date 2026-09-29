-- Prove2me | Theorems.Thm_lean_workbook_plus_50877
-- name    : lean_workbook_plus_50877
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/37016714-4e9c-4240-93aa-8561c4326f7f
-- statement:
--   Calculate $a_1+a_2+a_3+....+a_{100}$ where $a_n=3n^2+3n+1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50877 (a : ℕ → ℕ) (h : ∀ n, a n = 3 * n ^ 2 + 3 * n + 1) : ∑ i in Finset.range 101, a i = 1015050   :=  by sorry
