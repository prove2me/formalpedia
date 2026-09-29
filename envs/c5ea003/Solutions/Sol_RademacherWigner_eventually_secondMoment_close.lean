-- Prove2me | solution 1 for RademacherWigner.eventually_secondMoment_close
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:30:08.863796+00:00
-- url     : https://prove2.me/submissions/f4885ca2-99eb-46c6-ac92-45142cd6b0d9

-- Sol generated from Probability/WignerSemicircleLawLowOrder.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_card_fin_config
import Theorems.Thm_RademacherWigner_sqrt_inv_sq
import Theorems.Thm_RademacherWigner_trace_W_sq
import Theorems.Thm_WignerBridge_normalizedMoment_eq
import Theorems.Thm_WignerSemicircle_semicircleMoment_two
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
theorem solution(eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ g : Config N,
      |WignerBridge.normalizedMoment (W g) 2 - WignerSemicircle.semicircleMoment 2| < eps := by
  have hev : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / eps < (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (1 / eps)
  filter_upwards [hev, eventually_gt_atTop 0] with N hbig hN g
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [normalizedMoment_two g hN, WignerSemicircle.semicircleMoment_two]
  have : (1 : ℝ) / (N : ℝ) < eps := by
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ heps] at hbig
    linarith
  rw [show (1 : ℝ) - 1 / (N : ℝ) - 1 = -(1 / (N : ℝ)) by ring, abs_neg,
    abs_of_nonneg (by positivity)]
  exact this
