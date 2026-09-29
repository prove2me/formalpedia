-- Prove2me | Theorems.Thm_lean_workbook_plus_67722
-- name    : lean_workbook_plus_67722
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/322c5eea-13ea-46fb-8e37-cff023021fa9
-- statement:
--   Let S be subset of (0,1] such that: (1) \(\frac{1}{n} \in S\) ,for n every positive integer. (2)if x\in S ,then the average of x and \(\frac{1}{n}\) belongs S, which means \(\frac{x+\frac{1}{n}}{2}\in S\) . Should S contains all rationals of (0,1] ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67722 (S : Set ℝ) (hS : S ⊆ Set.Icc 0 1) (hn : ∀ n : ℕ, (1 / n : ℝ) ∈ S) (hx : ∀ x ∈ S, ∀ n : ℕ, (x + 1 / n) / 2 ∈ S) : S ⊆ Set.Icc (0 : ℚ) 1   :=  by sorry
