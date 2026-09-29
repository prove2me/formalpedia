-- Prove2me | solution 1 for TropicalSocialChoice.card_nondictatorial_coalitions
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:56:52.125036+00:00
-- url     : https://prove2.me/submissions/391a5524-e868-4322-a9e7-a178ebb8dbec

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
theorem solution(n : ℕ) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun s => s.Nonempty ∧ s.card ≠ 1)).card = 2 ^ n - 1 - n := by
  classical
  have hsmall : (Finset.univ.filter (fun s : Finset (Fin n) => s.card ≤ 1))
      = insert ∅ (Finset.univ.image (fun k : Fin n => ({k} : Finset (Fin n)))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image]
    constructor
    · intro hs
      rcases Nat.lt_or_ge s.card 1 with h | h
      · exact Or.inl (Finset.card_eq_zero.mp (by omega))
      · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
        exact Or.inr ⟨k, hk.symm⟩
    · rintro (rfl | ⟨k, rfl⟩) <;> simp
  have hcard : (Finset.univ.filter (fun s : Finset (Fin n) => s.card ≤ 1)).card = n + 1 := by
    rw [hsmall, Finset.card_insert_of_notMem, Finset.card_image_of_injective _
      Finset.singleton_injective, Finset.card_univ, Fintype.card_fin]
    simp
  have hfilter : (Finset.univ.filter (fun s : Finset (Fin n) => s.Nonempty ∧ s.card ≠ 1))
      = Finset.univ.filter (fun s : Finset (Fin n) => ¬ s.card ≤ 1) := by
    apply Finset.filter_congr
    intro s _
    constructor
    · rintro ⟨h1, h2⟩
      have := Finset.card_pos.mpr h1
      omega
    · intro h
      exact ⟨Finset.card_pos.mp (by omega), by omega⟩
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Finset (Fin n)))) (p := fun s : Finset (Fin n) => s.card ≤ 1)
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at htot
  rw [hfilter]
  omega
