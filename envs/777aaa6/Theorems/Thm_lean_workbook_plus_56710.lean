-- Prove2me | Theorems.Thm_lean_workbook_plus_56710
-- name    : lean_workbook_plus_56710
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/0e1f026c-9107-4572-a896-894640e91e67
-- statement:
--   By AM-GM we have: $\frac{1+2+\cdots + n}{n}>\sqrt[n]{1\cdot2\cdot3\cdot\cdots\cdot n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56710 : ∀ n : ℕ, (∑ i in Finset.range n, i) / n > (∏ i in Finset.range n, i) ^ (1 / n)   :=  by sorry
