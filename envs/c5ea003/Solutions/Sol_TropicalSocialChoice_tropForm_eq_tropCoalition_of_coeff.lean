-- Prove2me | solution 1 for TropicalSocialChoice.tropForm_eq_tropCoalition_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:13:53.581252+00:00
-- url     : https://prove2.me/submissions/efd1c390-36d0-429c-a4c5-4b85f5dcde46

-- Sol generated from Probability/TropicalSocialChoiceOligarchy.lean
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








open TropicalSocialChoice in
theorem solution{a : Fin n → TR} (h : ∀ i, a i = 0 ∨ a i = 1) :
    tropForm a = tropCoalition (tropSupport a) := by
  classical
  funext x
  have h1 : ∑ i ∈ tropSupport a, a i * x i = tropCoalition (tropSupport a) x :=
    Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2, one_mul]
  have h2 : ∑ i ∈ Finset.univ \ tropSupport a, a i * x i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have hne : a i ≠ 1 := by
        have := (Finset.mem_sdiff.mp hi).2
        simpa [tropSupport] using this
      rcases h i with h0 | h1'
      · rw [h0, zero_mul]
      · exact absurd h1' hne
  rw [tropForm, ← Finset.sum_sdiff (Finset.subset_univ (tropSupport a)), h1, h2, zero_add]
