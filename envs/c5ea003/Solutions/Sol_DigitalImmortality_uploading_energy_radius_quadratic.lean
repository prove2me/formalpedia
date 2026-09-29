-- Prove2me | solution 1 for DigitalImmortality.uploading_energy_radius_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:29:55.25799+00:00
-- url     : https://prove2.me/submissions/cb84c11f-5dec-4c0e-b6bf-32aa1fe80738

import Mathlib
import Definitions.Def_Novelty_MindEncodingBounds
open DigitalImmortality Real in
theorem solution (N : ℕ) (R E hbar c : ℝ) (hN : 1 ≤ N)
    (hbar_pos : 0 < hbar) (hc_pos : 0 < c)
    (hstore : (synapseSlots N : ℝ) ≤ bekensteinBits R E hbar c) :
    hbar * c * Real.log 2 / (4 * π) * ((N : ℝ) - 1) ^ 2 ≤ R * E := by
  unfold synapseSlots bekensteinBits at hstore
  rw [Nat.cast_choose_two] at hstore
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < hbar * c * Real.log 2 := by positivity
  -- the Bekenstein capacity must hold all `N(N-1)/2` synapse slots
  rw [le_div_iff₀ hK] at hstore
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- and `(N - 1)² ≤ N (N - 1)`
  have hsq : ((N : ℝ) - 1) ^ 2 ≤ (N : ℝ) * ((N : ℝ) - 1) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left hsq hK.le
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]
