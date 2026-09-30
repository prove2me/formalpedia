-- Prove2me | solution 1 for HirschCircuit.rowCircuitWalk_mono
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-08T18:47:52.673774+00:00
-- url     : https://prove2.me/submissions/5846b41e-2bb9-4860-b4f1-147b1ea02e4d

import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Hirsch

/-- Direct proof for padded row-circuit walk monotonicity. -/
theorem solution {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {L M : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (h : RowCircuitWalk a b L u v) (hLM : L ≤ M) :
    RowCircuitWalk a b M u v := by
  obtain ⟨w, hw0, hwL, hf, hs⟩ := h
  refine ⟨fun j => w (min j L), ?_, ?_, ?_, ?_⟩
  · simpa using hw0
  · simpa only [Nat.min_eq_right hLM] using hwL
  · intro j _
    exact hf _ (Nat.min_le_right _ _)
  · intro j _
    by_cases hj : j < L
    · simpa only [Nat.min_eq_left (Nat.le_of_lt hj),
        Nat.min_eq_left (Nat.succ_le_iff.mpr hj)] using hs j hj
    · left
      change w (min j L) = w (min (j + 1) L)
      rw [Nat.min_eq_right (Nat.le_of_not_gt hj),
        Nat.min_eq_right (by omega : L ≤ j + 1)]

#print axioms solution
