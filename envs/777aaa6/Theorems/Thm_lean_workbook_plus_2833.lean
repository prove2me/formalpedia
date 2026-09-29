-- Prove2me | Theorems.Thm_lean_workbook_plus_2833
-- name    : lean_workbook_plus_2833
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ea7f5068-32ff-4dd7-b7c5-fb8cc31798bf
-- statement:
--   Let $a_1,a_2,\cdots,a_n \in[0,1]$ $ (n\ge 2).$ Prove that $$\sum_{i=1}^{n}\left(\prod_{j\neq i}\sqrt{a^n_j }\sqrt{(1-a_i)}\right)\leq 1.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2833 (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 1) :
  ∑ i, (∏ j, if j ≠ i then Real.sqrt (a j ^ n) * Real.sqrt (1 - a i) else 0) ≤ 1   :=  by sorry
