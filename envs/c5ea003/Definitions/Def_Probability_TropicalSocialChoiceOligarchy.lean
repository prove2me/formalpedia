-- Prove2me | Definitions.Def_Probability_TropicalSocialChoiceOligarchy
-- name    : Probability_TropicalSocialChoiceOligarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:38.398033+00:00
-- url     : https://prove2.me/theorems/b0063115-ed61-40e2-a7ae-2ceba629ee08
-- title:
--   Aether Catalog definitions — Probability_TropicalSocialChoiceOligarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TropicalSocialChoiceOligarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TropicalSocialChoiceOligarchy.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
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

namespace TropicalSocialChoice

open Tropical

/-! ## Tropical arithmetic lemmas -/



/-! ## Diagonal idempotence and the oligarchy theorem -/

section Oligarchy

variable {n : ℕ}

/-- **Diagonal multiplicativity.**  Doubling everybody's cost doubles the social cost.
This is tropical multiplicativity `f (x ⊙ y) = f x ⊙ f y` restricted to `y = x`, and it is
the natural "no money illusion" requirement: the social aggregate is homogeneous of
degree one along the diagonal. -/
def TropDiagIdem (f : (Fin n → TR) → TR) : Prop := ∀ x, f (x * x) = f x * f x













end Oligarchy

/-! ## Scalar invariance: linearity without dictatorship -/

section ConstScale

variable {n : ℕ}

/-- **Scalar tropical invariance.**  Shifting every voter's costs by the same amount `c`
shifts the social cost by `c`.  This is tropical multiplicativity restricted to constant
profiles. -/
def TropConstScaleInv (f : (Fin n → TR) → TR) : Prop :=
  ∀ (c : TR) (x : Fin n → TR), f ((fun _ => c) * x) = c * f x






end ConstScale

/-! ## Sharpened dequantisation: the pivotal-voter correction -/

section Dequantisation

variable {ι : Type*}

open Finset in
/-- The *pivotal voters* of a profile: the members of the coalition whose cost attains the
minimum.  Their number is what measures the failure of the finite-temperature rule to be a
dictatorship. -/
noncomputable def pivotal (s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) : Finset ι := by
  classical
  exact s.filter fun i => y i = s.inf' hs y





end Dequantisation

end TropicalSocialChoice


