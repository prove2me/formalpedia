-- Prove2me | solution 1 for RademacherWigner.sqrt_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:16:11.606949+00:00
-- url     : https://prove2.me/submissions/bbb0aa5d-7bf9-4710-a74a-09aa884a4475

-- Sol generated from Probability/WignerSemicircleLawLowOrder.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
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
theorem solution(N : ℕ) : (Real.sqrt (N : ℝ))⁻¹ ^ 2 = ((N : ℝ))⁻¹ := by
  rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
