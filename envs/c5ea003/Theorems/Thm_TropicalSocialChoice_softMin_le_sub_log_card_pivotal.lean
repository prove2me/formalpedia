-- Prove2me | Theorems.Thm_TropicalSocialChoice_softMin_le_sub_log_card_pivotal
-- name    : TropicalSocialChoice.softMin_le_sub_log_card_pivotal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:17:24.759121+00:00
-- url     : https://prove2.me/theorems/ea1b58ea-8822-4941-a7a3-4cc70d19a768
-- title:
--   Sharpened upper bound for Maslov dequantisation.
-- statement:
--   **Sharpened upper bound for Maslov dequantisation.**  The Boltzmann aggregator is below
--   the tropical minimum by at least `log m / t`, where `m` is the number of *pivotal* voters.
--   Together with `softMin_bounds` this squeezes `softMin` between `min y − log (#s) / t` and
--   `min y − log m / t`: the deviation from the tropical (and, when `m = 1`, dictatorial) value
--   is governed by the number of tied voters.
--
--   ```lean
--   theorem TropicalSocialChoice.softMin_le_sub_log_card_pivotal(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t : ℝ}
--       (ht : 0 < t) :
--       softMin s t y ≤ s.inf' hs y - Real.log (pivotal s hs y).card / t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TropicalSocialChoiceOligarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TropicalSocialChoiceOligarchy.lean#L346

-- Thm stub generated from Probability/TropicalSocialChoiceOligarchy.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice II: the oligarchy classification

This file continues `Probability.TropicalSocialChoice`, where the *tropical Arrow
theorem* was proved: in the min-plus semiring `TR = Tropical (WithTop ℝ)`, a rule
`f : TRⁿ → TR` satisfying tropical IIA (`f (x ⊕ y) = f x ⊕ f y`), tropical Pareto
(`f (c,…,c) = c`) and tropical multiplicativity (`f (x ⊙ y) = f x ⊙ f y`) is the
projection onto a single voter.

Here we determine exactly what happens when tropical multiplicativity is replaced by two
strictly weaker requirements, resolving the first two conjectures recorded in
`FUTURE_DIRECTIONS.md` for tropically linear rules.

## Main results

* `TropDiagIdem`, `oligarchy_of_diagIdem`, `oligarchy_iff` : **diagonal idempotence**
  `f (x ⊙ x) = f x ⊙ f x` — multiplicativity restricted to the diagonal — replaces full
  multiplicativity, and the solution set jumps from the `n` dictators to the `2ⁿ − 1`
  *coalition (oligarchy) rules* `x ↦ ⨁_{i ∈ s} xᵢ`, `s ≠ ∅`.
* `tropCoalition_isTropDictatorial_iff` : a coalition rule is a dictatorship precisely
  when the coalition is a singleton, so for `n ≥ 2` the escape from Arrow's conclusion is
  genuine and its size is exactly `2ⁿ − 1 − n`
  (`card_nondictatorial_coalitions`).
* `TropConstScaleInv`, `isTropLinear_of_tropIIA_constScale`,
  `tropIIA_constScale_iff` : invariance under a *common* cost shift
  `f (c ⊙ x) = c ⊙ f x` still forces tropical linearity, but only pins the coefficients
  down to `⨁ᵢ aᵢ = 1`; the solution set is exactly the unanimous tropical linear forms,
  which for `n ≥ 2` contains non-dictatorial members
  (`exists_nondictatorial_tropConstScaleInv`).

* `softMin_le_sub_log_card_pivotal`, `softMin_lt_inf'_of_one_lt_card_pivotal` : a sharpened
  Maslov dequantisation bound.  The Boltzmann aggregator satisfies
  `min y − log (#s)/t ≤ softMin ≤ min y − log m / t`, where `m` is the number of *pivotal*
  (cost-minimising) voters; in particular a tie of two pivotal voters keeps the smoothed
  rule strictly below the tropical value by `log 2 / t` at every temperature.

Together with the tropical Arrow theorem this gives a complete picture of the axiom
hierarchy: full multiplicativity ⟹ dictator; diagonal multiplicativity ⟹ oligarchy;
scalar multiplicativity ⟹ arbitrary unanimous weights.
-/

open TropicalSocialChoice

open Tropical

/-! ## Tropical arithmetic lemmas -/



/-! ## Diagonal idempotence and the oligarchy theorem -/


variable {n : ℕ}















/-! ## Scalar invariance: linearity without dictatorship -/


variable {n : ℕ}








/-! ## Sharpened dequantisation: the pivotal-voter correction -/


variable {ι : Type*}

theorem TropicalSocialChoice.softMin_le_sub_log_card_pivotal(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t : ℝ}
    (ht : 0 < t) :
    softMin s t y ≤ s.inf' hs y - Real.log (pivotal s hs y).card / t := by sorry
