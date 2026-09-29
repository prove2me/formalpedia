-- Prove2me | solution 1 for sampleComplexity_linear_in_d
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:34:45.63591+00:00
-- url     : https://prove2.me/submissions/bacaed88-0e1c-4cff-b936-ad6ddf63284c

import Mathlib
import Definitions.Def_Bridges_ToposTheoreticML_Foundations

theorem solution {d₁ d₂ : ℕ} {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hd : d₁ ≤ d₂) :
    sampleComplexityBound d₁ ε δ ≤ sampleComplexityBound d₂ ε δ := by
  unfold sampleComplexityBound
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hlog : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (one_le_one_div hδ (le_of_lt hδ1))
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr hd) hε2.le) hlog
