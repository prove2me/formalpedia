-- Prove2me | solution 1 for RademacherWigner.expect_normalizedMoment_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:56:48.682557+00:00
-- url     : https://prove2.me/submissions/d4a39133-8a34-4c68-a3c7-6b6d1a8ea36b

-- Sol generated from Probability/WignerSemicircleLawLowOrder.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_card_fin_config
import Theorems.Thm_RademacherWigner_expect_const_mul
import Theorems.Thm_RademacherWigner_expect_trace_W_four
import Theorems.Thm_RademacherWigner_sqrt_inv_sq
import Theorems.Thm_WignerBridge_normalizedMoment_eq
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







/-! ### Convergence to the semicircle moments -/






open RademacherWigner in
theorem solution(N : ℕ) (hN : 0 < N) :
    expect (fun g : Config N => WignerBridge.normalizedMoment (W g) 4) =
      ((N : ℝ) - 1) * (2 * (N : ℝ) - 3) / (N : ℝ) ^ 2 := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hpow : (Real.sqrt (N : ℝ))⁻¹ ^ 4 = ((N : ℝ))⁻¹ ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sqrt_inv_sq]
  have hrw : ∀ g : Config N, WignerBridge.normalizedMoment (W g) 4 =
      (1 / (N : ℝ) * ((N : ℝ))⁻¹ ^ 2) * ((W g) ^ 4).trace := by
    intro g
    rw [WignerBridge.normalizedMoment_eq, card_fin_config, hpow]
  simp only [hrw]
  rw [expect_const_mul, expect_trace_W_four]
  field_simp
  ring
