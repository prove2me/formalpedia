-- Prove2me | Theorems.Thm_lean_workbook_plus_3225
-- name    : lean_workbook_plus_3225
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e3624aad-31a4-49cd-bead-5f70f395ad1f
-- statement:
--   Given a real number $a> 0$ . How many positive real solutions of the equation is $ a^{x}=x^{a} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3225 (a : ℝ) (ha : 0 < a) :  (∃! x : ℝ, (a^x = x^a ∧ 0 < x)) ∨ (∃ x1 x2 : ℝ, (a^x1 = x1^a ∧ 0 < x1) ∧  (a^x2 = x2^a ∧ 0 < x2) ∧ x1 ≠ x2)   :=  by sorry
