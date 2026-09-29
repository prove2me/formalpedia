-- Prove2me | solution 1 for Bridges.AttentionKneeEntropyBound.knee_ge_gate_sq_div_energy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T20:15:00.495374+00:00
-- url     : https://prove2.me/submissions/c81e9b49-528b-4d55-96b4-d5eb5f95fbdd

import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeGeometry
open Finset Bridges.AttentionKneeGeometry Bridges.AttentionKneeEntropyBound in
theorem solution {w : ℕ → ℝ} {g E : ℝ} (hg : 0 ≤ g) (hE : 0 < E)
    (hEbound : ∀ k, energy w k ≤ E) (hex : ∃ k, g ≤ mass w k) :
    g ^ 2 / E ≤ (knee w g : ℝ) := by
  -- the knee passes the gate
  have hK : g ≤ mass w (knee w g) := Nat.sInf_mem hex
  -- Cauchy–Schwarz: `mass(K)^2 ≤ K · energy(K) ≤ K E`
  have hcs : mass w (knee w g) ^ 2 ≤ (knee w g : ℝ) * energy w (knee w g) := by
    have := sq_sum_le_card_mul_sum_sq (s := range (knee w g)) (f := w)
    rw [card_range] at this
    exact this
  have hsq : g ^ 2 ≤ mass w (knee w g) ^ 2 := pow_le_pow_left₀ hg hK 2
  have hen : (knee w g : ℝ) * energy w (knee w g) ≤ (knee w g : ℝ) * E :=
    mul_le_mul_of_nonneg_left (hEbound _) (Nat.cast_nonneg _)
  rw [div_le_iff₀ hE]
  linarith
