-- Prove2me | Theorems.Thm_RateDial_stepCarrier_count_endpoints
-- name    : RateDial.stepCarrier_count_endpoints
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:50:47.366368+00:00
-- url     : https://prove2.me/theorems/de658a73-1ad9-419e-9dba-f523df8f6087
-- title:
--   Its window composition is maximally position dependent: a window starting at
-- statement:
--   Its window composition is maximally position dependent: a window starting at
--   `0` is entirely in class `true`, a window ending at `-1` entirely in class
--   `false`.
--
--   ```lean
--   theorem RateDial.stepCarrier_count_endpoints(L : ℕ) :
--       count stepCarrier 0 L true = L ∧ count stepCarrier (-(L : ℤ)) L true = 0 := by sorry
--
--
--   /-! ## The dichotomy -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/MixtureRateDialSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/MixtureRateDialSharpness.lean#L66

-- Thm stub generated from Shared/MixtureRateDialSharpness.lean
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

theorem RateDial.stepCarrier_count_endpoints(L : ℕ) :
    count stepCarrier 0 L true = L ∧ count stepCarrier (-(L : ℤ)) L true = 0 := by sorry
