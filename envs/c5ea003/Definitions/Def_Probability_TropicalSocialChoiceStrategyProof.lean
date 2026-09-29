-- Prove2me | Definitions.Def_Probability_TropicalSocialChoiceStrategyProof
-- name    : Probability_TropicalSocialChoiceStrategyProof
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:30.073268+00:00
-- url     : https://prove2.me/theorems/4deabb50-52c6-47e1-910c-40b159612ab6
-- title:
--   Aether Catalog definitions — Probability_TropicalSocialChoiceStrategyProof
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TropicalSocialChoiceStrategyProof`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TropicalSocialChoiceStrategyProof.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
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

namespace TropicalSocialChoice

open Tropical Finset

section StrategyProof

variable {n : ℕ}

/-- **Tropical strategy-proofness.**  If one voter reports a weakly higher cost and nobody
else changes their report, the social cost does not decrease: no voter gains by
understating a cost. -/
def TropStrategyProof (f : (Fin n → TR) → TR) : Prop :=
  ∀ (i : Fin n) (x x' : Fin n → TR), (∀ l, l ≠ i → x l = x' l) → x i ≤ x' i → f x ≤ f x'


/-- The handicapped two-voter rule `min (x₀, 1 + x₁)`: voter `1`'s reported cost carries a
unit penalty. -/
noncomputable def weightedRule : (Fin 2 → TR) → TR := tropForm ![1, ofReal 1]








end StrategyProof

end TropicalSocialChoice


