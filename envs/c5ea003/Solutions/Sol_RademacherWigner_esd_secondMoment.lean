-- Prove2me | solution 1 for RademacherWigner.esd_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-15T03:01:18.522453+00:00
-- url     : https://prove2.me/submissions/76019ca2-d4e8-4e24-9c09-de9fa5f758f8

-- Sol generated from Probability/WignerSemicircleLawLowOrder.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_W_isHermitian
import Theorems.Thm_RademacherWigner_card_fin_config
import Theorems.Thm_RademacherWigner_sqrt_inv_sq
import Theorems.Thm_RademacherWigner_trace_W_sq
import Theorems.Thm_WignerBridge_normalizedMoment_eq
import Theorems.Thm_WignerBridge_normalizedMoment_eq_sum_eigenvalues
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The semicircle law at orders two and four for the Rademacher Wigner ensemble

Combining

* `Probability.WignerSemicircleMoments` (moments of the semicircle law are Catalan
  numbers),
* `Probability.WignerTraceBridge` (empirical spectral moments = normalised traces),
* `Probability.WignerRademacherEnsemble` (exact trace moments of the ensemble),

this file proves the moment-method form of the Wigner semicircle law at the first
two nontrivial orders:

* `esd_secondMoment` : the second moment of the empirical spectral distribution of
  `W/√N` equals `1 - 1/N` for **every** realisation (perfect self-averaging), and
  converges to `∫ x² dsc(x) = C₁ = 1`;
* `expect_normalizedMoment_four` : the expected fourth moment equals
  `(N-1)(2N-3)/N²`, converging to `∫ x⁴ dsc(x) = C₂ = 2`;
* `eventually_secondMoment_close` : a (deterministic, hence in-probability)
  concentration statement for the second moment.
-/

open Matrix BigOperators Filter Topology

open RademacherWigner

variable {N : ℕ}



/-- The normalised second spectral moment is `1 - 1/N` for *every* realisation of
the ensemble: the second moment is perfectly self-averaging. -/
theorem normalizedMoment_two (g : Config N) (hN : 0 < N) :
    WignerBridge.normalizedMoment (W g) 2 = 1 - 1 / (N : ℝ) := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [WignerBridge.normalizedMoment_eq, trace_W_sq, card_fin_config, sqrt_inv_sq]
  field_simp




/-! ### Convergence to the semicircle moments -/






open RademacherWigner in
theorem solution(g : Config N) (hN : 0 < N) :
    (1 / (N : ℝ)) *
        ∑ i, ((W_isHermitian g).eigenvalues i / Real.sqrt (N : ℝ)) ^ 2 = 1 - 1 / (N : ℝ) := by
  have h := WignerBridge.normalizedMoment_eq_sum_eigenvalues (W_isHermitian g) 2
  rw [normalizedMoment_two g hN, Fintype.card_fin] at h
  rw [← h]
