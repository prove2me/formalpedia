-- Prove2me | Definitions.Def_Shared_MixtureRateDialSharpness
-- name    : Shared_MixtureRateDialSharpness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:04:47.119924+00:00
-- url     : https://prove2.me/theorems/9479bceb-0f0d-4f91-8b1d-52ee501f9453
-- title:
--   Aether Catalog definitions — Shared_MixtureRateDialSharpness
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.MixtureRateDialSharpness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/MixtureRateDialSharpness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_MixtureRateDialBaseline
import Definitions.Def_Shared_MixtureRateDialCells
import Definitions.Def_Shared_MixtureRateDialResidueCarriers

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

namespace RateDial

open Finset

/-! ## A positional reference family removes the excess entirely -/

/-- A two-cell reference family that *is* allowed to drift with `t`: cell `false`
carries the flat shape `B`, cell `true` carries the measured profile `T`. -/
noncomputable def positionalRef (B T : ℝ → ℝ) : Bool → ℝ → ℝ :=
  fun c t => if c then T t else B t



/-! ## An explicit aperiodic carrier with position-dependent composition -/

/-- The step carrier: the (aperiodic) classification `j ≥ 0`. -/
def stepCarrier : ℤ → Bool := fun j => decide (0 ≤ j)




/-! ## The dichotomy -/


end RateDial


