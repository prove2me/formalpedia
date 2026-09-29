-- Prove2me | solution 1 for RateDial.stepCarrier_count_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:39:39.484741+00:00
-- url     : https://prove2.me/submissions/1d2aed20-a4d3-49a2-841e-90e6615aa278

-- Sol generated from Shared/MixtureRateDialSharpness.lean
import Mathlib
import Definitions.Def_Shared_MixtureRateDialBaseline
import Definitions.Def_Shared_MixtureRateDialCells
import Definitions.Def_Shared_MixtureRateDialResidueCarriers
import Definitions.Def_Shared_MixtureRateDialSharpness

/-!
# Sharpness of the rate-dial theorem (Part IV): the flatness hypothesis is the whole story

Parts II and III show that a mixture over a *flat-composition* grid removes `0 %`
of a positional excess.  A negative result is only informative if the hypothesis
it turns on is not vacuous.  This file proves the two sharpness statements.

* `positional_mixture_removes_excess` — with a genuinely **positional** reference
  family (one whose cells drift with `t`), a two-cell mixture removes the excess
  *completely*.  So the `0 %` removal of paper 242 is a fact about the
  divisibility grid, not an artefact of the mixture formalism.
* `stepCarrier_count_endpoints`, `stepCarrier_composition_not_flat`,
  `stepCarrier_not_periodicClass` — an explicit aperiodic carrier (`j ≥ 0`) whose
  window composition *does* depend on position, hence not `m`-periodic for any
  `m ≥ 1`; the class of position dials that Part III excludes is nonempty, and it
  lives exactly outside the residue world.
* `rate_dial_dichotomy` — the two halves side by side: flat composition forces
  `0 %` removal, non-flat composition can force `100 %` removal.
-/

open RateDial

open Finset

/-! ## A positional reference family removes the excess entirely -/




/-! ## An explicit aperiodic carrier with position-dependent composition -/





/-! ## The dichotomy -/



open RateDial in
theorem solution(L : ℕ) :
    count stepCarrier 0 L true = L ∧ count stepCarrier (-(L : ℤ)) L true = 0 := by
  constructor
  · have : ∀ i ∈ Finset.range L, (if stepCarrier (0 + (i : ℤ)) = true then 1 else 0) = 1 := by
      intro i _
      simp [stepCarrier]
    rw [count, Finset.sum_congr rfl this]
    simp
  · have : ∀ i ∈ Finset.range L, (if stepCarrier (-(L : ℤ) + (i : ℤ)) = true then 1 else 0) = 0 := by
      intro i hi
      have hiL : (i : ℤ) < (L : ℤ) := by exact_mod_cast Finset.mem_range.mp hi
      have hneg : ¬ (0 : ℤ) ≤ -(L : ℤ) + (i : ℤ) := by omega
      simp [stepCarrier, hneg]
    rw [count, Finset.sum_congr rfl this]
    simp
