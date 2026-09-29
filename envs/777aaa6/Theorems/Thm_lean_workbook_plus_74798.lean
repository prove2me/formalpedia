-- Prove2me | Theorems.Thm_lean_workbook_plus_74798
-- name    : lean_workbook_plus_74798
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d6397834-5519-4ee7-b7b4-a08eec02298d
-- statement:
--   4. $\left ( \log_{a}b\right) \left(\log_{c} d\right) = \left(\log_{a} d \right) \left(\log_{c} b\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74798 (a b c d : ℝ) : (a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a ≠ 1 ∧ c ≠ 1) → (Real.logb a b) * (Real.logb c d) = (Real.logb a d) * (Real.logb c b)   :=  by sorry
