-- Prove2me | solution 1 for RademacherWigner.tendsto_expected_fourthMoment
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:20.767316+00:00
-- url     : https://prove2.me/submissions/d5dbcb39-8cb2-4e40-9803-bc2a41eba079

-- Sol generated from Probability/WignerSemicircleLawLowOrder.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_expect_normalizedMoment_four
import Theorems.Thm_WignerSemicircle_semicircleMoment_four
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
theorem solution:
    Tendsto (fun N : ℕ => expect (fun g : Config N => WignerBridge.normalizedMoment (W g) 4))
      atTop (𝓝 (WignerSemicircle.semicircleMoment 4)) := by
  rw [WignerSemicircle.semicircleMoment_four]
  have hlim : Tendsto (fun N : ℕ => 2 - 5 * (1 / (N : ℝ)) + 3 * (1 / (N : ℝ)) ^ 2) atTop
      (𝓝 2) := by
    have h : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun N : ℕ => (2 : ℝ) - 5 * (1 / (N : ℝ)) + 3 * (1 / (N : ℝ)) ^ 2) atTop
        (𝓝 (2 - 5 * 0 + 3 * 0 ^ 2)) :=
      ((tendsto_const_nhds.sub (tendsto_const_nhds.mul h)).add
        (tendsto_const_nhds.mul (h.pow 2)))
    simpa using h2
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [expect_normalizedMoment_four N hN]
  field_simp
  ring
