-- Prove2me | Theorems.Thm_lean_workbook_plus_21774
-- name    : lean_workbook_plus_21774
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/affe610d-1fb8-4264-8924-9dc8f52fb962
-- statement:
--   Prove the logarithmic identity: $(\log_a b)(\log_b c)=\log_a c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21774 : ∀ a b c : ℝ, (a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ 1 ∧ b ≠ 1 ∧ c ≠ 1) →  (Real.log b / Real.log a) * (Real.log c / Real.log b) = (Real.log c / Real.log a)   :=  by sorry
