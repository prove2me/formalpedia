-- Prove2me | Theorems.Thm_TropicalSocialChoice_exists_two_active_coeffs
-- name    : TropicalSocialChoice.exists_two_active_coeffs
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:16:05.488824+00:00
-- url     : https://prove2.me/theorems/f27ef3bf-dfa0-4375-9b17-3b1e51e136e8
-- title:
--   A unanimous tropical linear rule which is not a dictatorship has, besides a voter with
-- statement:
--   A unanimous tropical linear rule which is not a dictatorship has, besides a voter with
--   coefficient `1`, a second voter whose coefficient is a finite nonnegative handicap.
--
--   ```lean
--   theorem TropicalSocialChoice.exists_two_active_coeffs{a : Fin n → TR} (hsum : ∑ i, a i = 1)
--       (hnd : ¬ IsTropDictatorial (tropForm a)) :
--       ∃ k j : Fin n, j ≠ k ∧ a k = 1 ∧ ∃ c : ℝ, 0 ≤ c ∧ a j = ofReal c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TropicalSocialChoiceOrdinal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TropicalSocialChoiceOrdinal.lean#L69

-- Thm stub generated from Probability/TropicalSocialChoiceOrdinal.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Definitions.Def_Probability_TropicalSocialChoiceOrdinal
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

open TropicalSocialChoice

open Tropical Finset


variable {n : ℕ}

/-! ### A tropical linear form is the minimum of its terms -/




/-! ### Two active voters -/

theorem TropicalSocialChoice.exists_two_active_coeffs{a : Fin n → TR} (hsum : ∑ i, a i = 1)
    (hnd : ¬ IsTropDictatorial (tropForm a)) :
    ∃ k j : Fin n, j ≠ k ∧ a k = 1 ∧ ∃ c : ℝ, 0 ≤ c ∧ a j = ofReal c := by sorry
