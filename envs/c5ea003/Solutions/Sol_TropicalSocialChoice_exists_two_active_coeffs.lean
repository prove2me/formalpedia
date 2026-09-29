-- Prove2me | solution 1 for TropicalSocialChoice.exists_two_active_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:00:10.953652+00:00
-- url     : https://prove2.me/submissions/07915fb7-dbfb-4678-bab6-2515bc34a431

-- Sol generated from Probability/TropicalSocialChoiceOrdinal.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Definitions.Def_Probability_TropicalSocialChoiceOligarchy
import Definitions.Def_Probability_TropicalSocialChoiceOrdinal
import Theorems.Thm_TropicalSocialChoice_exists_coeff_eq_one
import Theorems.Thm_TropicalSocialChoice_one_le_coeff
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice VI: the ordinal price of the tropical escape

`Probability.TropicalSocialChoice` showed that the tropical axioms admit non-dictatorial
rules once tropical multiplicativity is dropped (e.g. the Rawlsian minimum rule), and that
this particular rule violates *classical* (ordinal) independence of irrelevant
alternatives, so that Arrow's theorem is not contradicted.

Conjecture 4 of `FUTURE_DIRECTIONS.md` asserted that this is a general phenomenon: **every**
non-dictatorial unanimous tropical linear rule violates classical IIA.  This file proves it,
and deduces Arrow's theorem in the form

  tropical linearity + tropical Pareto + ordinal IIA ⟹ dictator.

## Main results

* `le_tropForm`, `tropForm_le` : a tropical linear form is the minimum of its terms.
* `exists_two_active_coeffs` : a unanimous tropical linear rule that is not a dictatorship
  has a voter `k` with coefficient `1` and a *second* voter `j ≠ k` with a finite
  coefficient `c ≥ 0`.
* `nondictatorial_violates_classical_IIA` : **Conjecture 4, proved.**  Such a rule fails
  classical IIA: two cost profiles that induce the same individual rankings of two
  alternatives are ranked oppositely by society.  Voter `j`'s *intensity* of preference,
  not merely its direction, moves the social ranking.
* `arrow_recovered` : consequently the rules satisfying tropical linearity, tropical Pareto
  and classical ordinal IIA are exactly the dictators — Arrow's theorem, recovered inside
  the tropical framework.
-/

open TropicalSocialChoice

open Tropical Finset


variable {n : ℕ}

/-! ### A tropical linear form is the minimum of its terms -/




/-! ### Two active voters -/

/-- If all coefficients other than `a k = 1` vanish, the rule is the dictatorship of `k`. -/
theorem tropForm_eq_tropDictator_of_coeffs {a : Fin n → TR} {k : Fin n} (hk : a k = 1)
    (hzero : ∀ j, j ≠ k → a j = 0) : tropForm a = tropDictator k := by
  classical
  funext x
  rw [tropForm, Finset.sum_eq_single k]
  · rw [hk, one_mul]; rfl
  · intro b _ hb; rw [hzero b hb, zero_mul]
  · intro h; simp at h


/-! ### Classical independence of irrelevant alternatives -/








open TropicalSocialChoice in
theorem solution{a : Fin n → TR} (hsum : ∑ i, a i = 1)
    (hnd : ¬ IsTropDictatorial (tropForm a)) :
    ∃ k j : Fin n, j ≠ k ∧ a k = 1 ∧ ∃ c : ℝ, 0 ≤ c ∧ a j = ofReal c := by
  obtain ⟨k, hk⟩ := exists_coeff_eq_one hsum
  by_cases hall : ∀ j, j ≠ k → a j = 0
  · exact absurd ⟨k, tropForm_eq_tropDictator_of_coeffs hk hall⟩ hnd
  · push_neg at hall
    obtain ⟨j, hjk, hj⟩ := hall
    have hne : untrop (a j) ≠ ⊤ := fun ht => hj (untrop_injective (by rw [ht]; rfl))
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hne
    have hac : a j = ofReal c := untrop_injective (by rw [← hc]; rfl)
    refine ⟨k, j, hjk, hk, c, ?_, hac⟩
    have h1 : (1 : TR) ≤ a j := one_le_coeff hsum j
    rw [hac, ← untrop_le_iff] at h1
    have : ((0 : ℝ) : WithTop ℝ) ≤ ((c : ℝ) : WithTop ℝ) := h1
    exact_mod_cast this
