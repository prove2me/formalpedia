-- Prove2me | solution 1 for TropicalSocialChoice.softMin_le_sub_log_card_pivotal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:04:26.972588+00:00
-- url     : https://prove2.me/submissions/305400ec-7c30-49a9-99c1-dbd496290b52

-- Sol generated from Probability/TropicalSocialChoiceOligarchy.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Theorems.Thm_TropicalSocialChoice_pivotal_nonempty
import Theorems.Thm_TropicalSocialChoice_pivotal_subset
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
theorem solution(s : Finset ι) (hs : s.Nonempty) (y : ι → ℝ) {t : ℝ}
    (ht : 0 < t) :
    softMin s t y ≤ s.inf' hs y - Real.log (pivotal s hs y).card / t := by
  classical
  set m := s.inf' hs y with hm
  set P := pivotal s hs y with hP
  have hPs : P ⊆ s := pivotal_subset s hs y
  have hPne : P.Nonempty := pivotal_nonempty s hs y
  have hsum : ∑ i ∈ P, Real.exp (-(t * y i)) = (P.card : ℝ) * Real.exp (-(t * m)) := by
    rw [Finset.sum_congr rfl fun i hi => by
      rw [show y i = m from (Finset.mem_filter.mp hi).2]]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hle : (P.card : ℝ) * Real.exp (-(t * m)) ≤ ∑ i ∈ s, Real.exp (-(t * y i)) := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hPs fun i _ _ => (Real.exp_pos _).le
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hPne
  have hposP : (0 : ℝ) < (P.card : ℝ) * Real.exp (-(t * m)) :=
    mul_pos hcard (Real.exp_pos _)
  have hlog : Real.log P.card + -(t * m) ≤ Real.log (∑ i ∈ s, Real.exp (-(t * y i))) := by
    have h := Real.log_le_log hposP hle
    rwa [Real.log_mul (ne_of_gt hcard) (Real.exp_ne_zero _), Real.log_exp] at h
  have hinv : (0 : ℝ) ≤ 1 / t := by positivity
  have h := mul_le_mul_of_nonneg_left hlog hinv
  have e : (1 / t) * (Real.log P.card + -(t * m)) = Real.log P.card / t - m := by
    field_simp; ring
  rw [e] at h
  simp only [softMin]
  linarith
