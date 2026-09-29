-- Prove2me | Theorems.Thm_TropicalSocialChoice_weightedRule_ne_tropCoalition
-- name    : TropicalSocialChoice.weightedRule_ne_tropCoalition
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:19:39.681042+00:00
-- url     : https://prove2.me/theorems/e86c9579-f649-4494-911a-349e144fb1cb
-- title:
--   The handicap makes the rule differ from every coalition rule: on the profile where
-- statement:
--   The handicap makes the rule differ from every coalition rule: on the profile where
--   voter `0` is unavailable (cost `⊤`) and voter `1` reports the neutral cost, the rule
--   returns the penalised cost `1`, which no coalition rule ever produces.
--
--   ```lean
--   theorem TropicalSocialChoice.weightedRule_ne_tropCoalition(s : Finset (Fin 2)) : weightedRule ≠ tropCoalition s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TropicalSocialChoiceStrategyProof.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TropicalSocialChoiceStrategyProof.lean#L73

-- Thm stub generated from Probability/TropicalSocialChoiceStrategyProof.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Definitions.Def_Probability_TropicalSocialChoiceStrategyProof
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice VII: strategy-proofness is not restrictive

Conjecture 3 of `FUTURE_DIRECTIONS.md` proposed a tropical Gibbard–Satterthwaite theorem:
calling `f : TRⁿ → TR` *tropically strategy-proof* when raising one voter's reported cost
never lowers the social cost, it conjectured that tropically strategy-proof, unanimous,
tropically linear rules are exactly the coalition rules.

This file settles the conjecture: **the monotonicity condition has no bite at all.**

## Main results

* `TropStrategyProof`, `IsTropLinear.tropStrategyProof` : every tropical linear form is
  tropically strategy-proof, so the axiom is implied by linearity and adds nothing.
* `weightedRule_tropStrategyProof`, `weightedRule_ne_tropCoalition` : the handicapped rule
  `f (x₀, x₁) = min (x₀, 1 + x₁)` (voter `1` carries a unit cost penalty) is tropically
  linear, unanimous and strategy-proof, but is not a coalition rule.
* `not_tropical_gibbard_satterthwaite` : Conjecture 3 refuted.  Adding tropical
  strategy-proofness to tropical linearity and unanimity does not force a coalition rule;
  diagonal idempotence (`oligarchy_iff`) genuinely is a stronger requirement.
-/

open TropicalSocialChoice

open Tropical Finset


variable {n : ℕ}

theorem TropicalSocialChoice.weightedRule_ne_tropCoalition(s : Finset (Fin 2)) : weightedRule ≠ tropCoalition s := by sorry
