-- Prove2me | solution 1 for TropicalSocialChoice.distortedRule_not_isTropLinear
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:12:53.420083+00:00
-- url     : https://prove2.me/submissions/cf4f4eb2-d960-459f-9526-155735313492

-- Sol generated from Probability/TropicalSocialChoiceNonlinear.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceNonlinear
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Theorems.Thm_TropicalSocialChoice_ofReal_injective
import Theorems.Thm_TropicalSocialChoice_tropForm_apply_single
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





@[simp] theorem phiT_zero : phiT 0 = 0 := by
  apply untrop_injective
  simp [phiT]

@[simp] theorem phiT_one : phiT 1 = 1 := by
  apply untrop_injective
  have h : untrop (1 : TR) = ((0 : ℝ) : WithTop ℝ) := rfl
  simp only [phiT, untrop_trop, h, WithTop.map_coe]
  rw [show phiR 0 = 0 by unfold phiR; norm_num]

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







open TropicalSocialChoice in
theorem solution: ¬ IsTropLinear distortedRule := by
  rintro ⟨a, ha⟩
  have e10 : (Pi.single (1 : Fin 2) (1 : TR) : Fin 2 → TR) 0 = 0 :=
    Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide) 1
  have e11 : (Pi.single (1 : Fin 2) (1 : TR) : Fin 2 → TR) 1 = 1 := Pi.single_eq_same 1 1
  have e00 : (Pi.single (0 : Fin 2) (1 : TR) : Fin 2 → TR) 0 = 1 := Pi.single_eq_same 0 1
  have e01 : (Pi.single (0 : Fin 2) (1 : TR) : Fin 2 → TR) 1 = 0 :=
    Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide) 1
  have ha1 : a 1 = 1 := by
    have h := (tropForm_apply_single a 1).symm.trans (ha (Pi.single 1 1)).symm
    rw [distortedRule_apply, e10, e11, phiT_one, zero_add] at h
    exact h
  have ha0 : a 0 = 1 := by
    have h := (tropForm_apply_single a 0).symm.trans (ha (Pi.single 0 1)).symm
    rw [distortedRule_apply, e00, e01, phiT_zero, add_zero] at h
    exact h
  have hval : distortedRule testProfile = ofReal 1 := by
    rw [ha testProfile, tropForm, Fin.sum_univ_two, ha0, ha1, one_mul, one_mul,
      testProfile_zero, testProfile_one, zero_add]
  rw [distortedRule_testProfile] at hval
  have : (2 : ℝ) = 1 := ofReal_injective hval
  norm_num at this
