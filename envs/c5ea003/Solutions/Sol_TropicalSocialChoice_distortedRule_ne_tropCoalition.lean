-- Prove2me | solution 1 for TropicalSocialChoice.distortedRule_ne_tropCoalition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:12:52.929985+00:00
-- url     : https://prove2.me/submissions/5b390dbd-0126-48cc-87a4-c1a839cf058e

-- Sol generated from Probability/TropicalSocialChoiceNonlinear.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceNonlinear
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Theorems.Thm_TropicalSocialChoice_ofReal_injective
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice IV: linearity cannot be dropped from the oligarchy theorem

`Probability.TropicalSocialChoiceOligarchy` proved the *tropical oligarchy theorem*: a
**tropically linear**, unanimous, diagonally idempotent rule `f : TRⁿ → TR` is the minimum
rule `x ↦ ⨁_{i ∈ s} xᵢ` of a nonempty coalition `s`.  Conjecture 1 of
`FUTURE_DIRECTIONS.md` asked whether the linearity hypothesis is redundant, as it is for
the full multiplicativity axiom (`isTropLinear_of_tropIIA`).

**It is not.**  This file constructs an explicit counterexample and thereby refutes
Conjecture 1.

The counterexample is the two-voter rule
`f (x₀, x₁) = x₀ ⊕ φ(x₁) = min (x₀, φ(x₁))`,
where `φ` is the piecewise-linear cost distortion `φ(r) = 2r` for `r ≥ 0` and `φ(r) = r/2`
for `r < 0` (and `φ(∞) = ∞`).  The point is that `φ` is monotone (hence `⊕`-additive) and
*doubling-homogeneous*, `φ(2r) = 2φ(r)`, but not a translation `r ↦ a + r`.  Diagonal
idempotence only ever tests `f` along the doubling map, so it cannot see the difference,
whereas full multiplicativity would.

## Main results

* `phiT_add`, `phiT_mul_self`, `phiT_ge` : the distortion `φ` preserves tropical addition,
  is homogeneous along the diagonal, and is a *penalty* (`c ≤ φ c`).
* `distortedRule_tropIIA`, `distortedRule_tropPareto`, `distortedRule_tropDiagIdem` : the
  rule satisfies tropical IIA, tropical Pareto and diagonal idempotence.
* `distortedRule_not_isTropLinear` : it is **not** tropically linear.
* `distortedRule_ne_tropCoalition` : it differs from every coalition rule.
* `not_oligarchy_of_tropIIA_tropDiagIdem` : the refutation of Conjecture 1 — there is a
  rule satisfying `TropIIA`, `TropPareto` and `TropDiagIdem` which is not a coalition rule
  (and not even tropically linear).  Hence the oligarchy theorem genuinely needs its
  linearity hypothesis, in sharp contrast with the tropical Arrow theorem.
-/

open TropicalSocialChoice

open Tropical

/-! ## A monotone, doubling-homogeneous cost distortion which is not a translation -/






/-- `φ` is not a translation: it is not of the form `r ↦ a + r`. -/
theorem phiR_one_two : phiR 1 = 2 ∧ phiR 2 = 4 := by
  constructor <;> · unfold phiR; norm_num







theorem phiT_ofReal (r : ℝ) : phiT (ofReal r) = ofReal (phiR r) := by
  apply untrop_injective
  simp [phiT, ofReal]

/-! ## The counterexample rule -/


theorem distortedRule_apply (x : Fin 2 → TR) : distortedRule x = x 0 + phiT (x 1) := rfl





theorem testProfile_zero : testProfile 0 = 0 := rfl
theorem testProfile_one : testProfile 1 = ofReal 1 := rfl

theorem distortedRule_testProfile : distortedRule testProfile = ofReal 2 := by
  rw [distortedRule_apply, testProfile_zero, testProfile_one, zero_add, phiT_ofReal,
    show phiR 1 = 2 from phiR_one_two.1]

theorem ofReal_ne_zero (r : ℝ) : ofReal r ≠ 0 := by
  intro h
  have := congrArg untrop h
  simp only [ofReal, untrop_trop] at this
  exact (WithTop.coe_ne_top) this






open TropicalSocialChoice in
theorem solution(s : Finset (Fin 2)) :
    distortedRule ≠ tropCoalition s := by
  intro hs
  have hcases : ∀ t : Finset (Fin 2), t = ∅ ∨ t = {0} ∨ t = {1} ∨ t = {0, 1} := by decide
  have hval : distortedRule testProfile = ofReal 2 := distortedRule_testProfile
  rw [hs] at hval
  rcases hcases s with rfl | rfl | rfl | rfl
  · rw [tropCoalition, Finset.sum_empty] at hval
    exact ofReal_ne_zero 2 hval.symm
  · rw [tropCoalition, Finset.sum_singleton, testProfile_zero] at hval
    exact ofReal_ne_zero 2 hval.symm
  · rw [tropCoalition, Finset.sum_singleton, testProfile_one] at hval
    have : (2 : ℝ) = 1 := ofReal_injective hval.symm
    norm_num at this
  · rw [tropCoalition, show ({0, 1} : Finset (Fin 2)) = Finset.univ from rfl, Fin.sum_univ_two,
      testProfile_zero, testProfile_one, zero_add] at hval
    have : (2 : ℝ) = 1 := ofReal_injective hval.symm
    norm_num at this
