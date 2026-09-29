-- Prove2me | solution 1 for lean_workbook_plus_49815
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:57:00.489917+00:00
-- url     : https://prove2.me/submissions/dcbc0002-67fd-4014-8c8a-388a5dd3c4b1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (h : a ≥ b ∧ b ≥ c ∨ b ≥ c ∧ c ≥ a ∨ c ≥ a ∧ a ≥ b) : (a - b) * (b - c) * (c - a) ≤ 0 := by
  rcases h with ⟨hab, hbc⟩ | ⟨hbc, hca⟩ | ⟨hca, hab⟩
  · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) (by linarith)) (by linarith)
  · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) (by linarith)
  · exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (by linarith)
