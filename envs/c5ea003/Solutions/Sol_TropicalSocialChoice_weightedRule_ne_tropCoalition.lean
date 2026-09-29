-- Prove2me | solution 1 for TropicalSocialChoice.weightedRule_ne_tropCoalition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:23:11.807978+00:00
-- url     : https://prove2.me/submissions/fc50ac98-30bc-4ec1-9830-a97baef8db5e

-- Sol generated from Probability/TropicalSocialChoiceStrategyProof.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Definitions.Def_Probability_TropicalSocialChoiceStrategyProof
import Theorems.Thm_TropicalSocialChoice_ofReal_injective
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













open TropicalSocialChoice in
theorem solution(s : Finset (Fin 2)) : weightedRule ≠ tropCoalition s := by
  classical
  intro hs
  have hval : weightedRule ![0, 1] = ofReal 1 := by
    rw [weightedRule, tropForm, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_zero, mul_one, zero_add]
  rw [hs] at hval
  have h0 : (![0, 1] : Fin 2 → TR) 0 = 0 := rfl
  have h1 : (![0, 1] : Fin 2 → TR) 1 = 1 := rfl
  have hne0 : ofReal 1 ≠ (0 : TR) := by
    intro h
    have := congrArg untrop h
    simp only [ofReal, untrop_trop] at this
    exact WithTop.coe_ne_top this
  have hne1 : ofReal 1 ≠ (1 : TR) := by
    intro h
    have : (1 : ℝ) = 0 := ofReal_injective (by rw [h]; rfl)
    norm_num at this
  have hcases : ∀ t : Finset (Fin 2), t = ∅ ∨ t = {0} ∨ t = {1} ∨ t = {0, 1} := by decide
  rcases hcases s with rfl | rfl | rfl | rfl
  · rw [tropCoalition, Finset.sum_empty] at hval
    exact hne0 hval.symm
  · rw [tropCoalition, Finset.sum_singleton, h0] at hval
    exact hne0 hval.symm
  · rw [tropCoalition, Finset.sum_singleton, h1] at hval
    exact hne1 hval.symm
  · rw [tropCoalition, show ({0, 1} : Finset (Fin 2)) = Finset.univ from rfl, Fin.sum_univ_two,
      h0, h1, zero_add] at hval
    exact hne1 hval.symm
