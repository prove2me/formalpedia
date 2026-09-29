-- Prove2me | solution 1 for lean_workbook_plus_32277
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:23:36.666161+00:00
-- url     : https://prove2.me/submissions/c4b3a80a-78de-4b73-b536-0bc5f37e066b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b c : ℝ, a ∈ Set.Icc 0 2 ∧ b ∈ Set.Icc 0 2 ∧ c ∈ Set.Icc 0 2 → (2 - a) * (2 - b) * (2 - c) ≥ 0 := by
  rintro a b c ⟨ha, hb, hc⟩
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)) (sub_nonneg.mpr hc.2)
