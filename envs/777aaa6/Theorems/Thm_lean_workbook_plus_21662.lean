-- Prove2me | Theorems.Thm_lean_workbook_plus_21662
-- name    : lean_workbook_plus_21662
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/eef53372-20d7-482e-9c19-e7a5300e069c
-- statement:
--   Prove that $(1-\frac{1}{2})(1- \frac{1}{3})(1-\frac{1}{4})...(1- \frac{1}{n}) = \frac{1}{n}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21662 : ∀ n : ℕ, (∏ k in Finset.Icc 2 n, (1 - 1 / k)) = 1 / n   :=  by sorry
