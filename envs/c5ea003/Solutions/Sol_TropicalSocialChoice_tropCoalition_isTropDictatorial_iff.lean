-- Prove2me | solution 1 for TropicalSocialChoice.tropCoalition_isTropDictatorial_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:10:49.196987+00:00
-- url     : https://prove2.me/submissions/8a33ba68-96a3-4d27-87d7-11014485a11c

-- Sol generated from Probability/TropicalSocialChoiceOligarchy.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Theorems.Thm_TropicalSocialChoice_tropCoalition_not_dictatorial
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









/-- The singleton coalition rule is the dictator. -/
theorem tropCoalition_singleton (k : Fin n) : tropCoalition {k} = tropDictator k := by
  funext x
  rw [tropCoalition, Finset.sum_singleton]
  rfl


/-- The empty coalition (the constant rule `x ↦ ⊤`) is not a dictatorship. -/
theorem tropCoalition_empty_not_dictatorial :
    ¬ IsTropDictatorial (tropCoalition (∅ : Finset (Fin n))) := by
  rintro ⟨m, hm⟩
  have h1 : tropCoalition (∅ : Finset (Fin n)) (Pi.single m 1) = 0 := by
    simp [tropCoalition]
  rw [hm] at h1
  have h2 : tropDictator m (Pi.single m (1 : TR)) = 1 := Pi.single_eq_same _ _
  rw [h2] at h1
  exact one_ne_zero h1




/-! ## Scalar invariance: linearity without dictatorship -/


variable {n : ℕ}








/-! ## Sharpened dequantisation: the pivotal-voter correction -/


variable {ι : Type*}








open TropicalSocialChoice in
theorem solution(s : Finset (Fin n)) :
    IsTropDictatorial (tropCoalition s) ↔ s.card = 1 := by
  classical
  constructor
  · intro hdict
    rcases Nat.lt_or_ge s.card 1 with hlt | hge
    · have hs : s = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hs
      exact absurd hdict tropCoalition_empty_not_dictatorial
    · rcases eq_or_lt_of_le hge with heq | hlt2
      · exact heq.symm
      · obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hlt2
        exact absurd hdict (tropCoalition_not_dictatorial hj hk hjk)
  · intro hcard
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
    exact ⟨k, by rw [hk, tropCoalition_singleton]⟩
