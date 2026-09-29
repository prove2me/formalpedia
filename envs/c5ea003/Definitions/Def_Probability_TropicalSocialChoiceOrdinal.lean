-- Prove2me | Definitions.Def_Probability_TropicalSocialChoiceOrdinal
-- name    : Probability_TropicalSocialChoiceOrdinal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:20.625238+00:00
-- url     : https://prove2.me/theorems/7a2c87c9-75b8-4c1d-a272-fdddb78cf699
-- title:
--   Aether Catalog definitions — Probability_TropicalSocialChoiceOrdinal
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TropicalSocialChoiceOrdinal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TropicalSocialChoiceOrdinal.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice VI: the ordinal price of the tropical escape

`Probability.TropicalSocialChoice` showed that the tropical axioms admit non-dictatorial
rules once tropical multiplicativity is dropped (e.g. the Rawlsian minimum rule), and that
this particular rule violates *classical* (ordinal) independence of irrelevant
alternatives, so that Arrow's theorem is not contradicted.

Conjecture 4 of `FUTURE_DIRECTIONS.md` asserted that this is a general phenomenon: **every**
non-dictatorial unanimous tropical linear rule violates classical IIA.  This file proves it,
and deduces Arrow's theorem in the form

  tropical linearity + tropical Pareto + ordinal IIA ⟹ dictator.

## Main results

* `le_tropForm`, `tropForm_le` : a tropical linear form is the minimum of its terms.
* `exists_two_active_coeffs` : a unanimous tropical linear rule that is not a dictatorship
  has a voter `k` with coefficient `1` and a *second* voter `j ≠ k` with a finite
  coefficient `c ≥ 0`.
* `nondictatorial_violates_classical_IIA` : **Conjecture 4, proved.**  Such a rule fails
  classical IIA: two cost profiles that induce the same individual rankings of two
  alternatives are ranked oppositely by society.  Voter `j`'s *intensity* of preference,
  not merely its direction, moves the social ranking.
* `arrow_recovered` : consequently the rules satisfying tropical linearity, tropical Pareto
  and classical ordinal IIA are exactly the dictators — Arrow's theorem, recovered inside
  the tropical framework.
-/

namespace TropicalSocialChoice

open Tropical Finset

section Ordinal

variable {n : ℕ}

/-! ### A tropical linear form is the minimum of its terms -/




/-! ### Two active voters -/



/-! ### Classical independence of irrelevant alternatives -/

/-- Classical (ordinal) IIA on two alternatives: the social ranking of the two
alternatives depends only on the individual *rankings* of those alternatives, not on the
cardinal costs. -/
def ClassicalIIA (f : (Fin n → TR) → TR) : Prop :=
  ∀ u v : Fin n → Bool → ℝ, (∀ i, (u i true ≤ u i false ↔ v i true ≤ v i false)) →
    (SocPrefers f u true false ↔ SocPrefers f v true false)





end Ordinal

end TropicalSocialChoice


