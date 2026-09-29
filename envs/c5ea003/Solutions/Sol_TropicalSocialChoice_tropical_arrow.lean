-- Prove2me | solution 1 for TropicalSocialChoice.tropical_arrow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:13:55.272885+00:00
-- url     : https://prove2.me/submissions/cf1dd305-ac7e-41c0-bf59-307e2d10117c

-- Sol generated from Probability/TropicalSocialChoice.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
import Theorems.Thm_TropicalSocialChoice_coeff_mul_coeff_eq_zero
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Tropical social choice: a min-plus Arrow theorem

We work in the tropical (min-plus) semiring `TR = Tropical (WithTop ℝ)` of *extended
costs*: tropical addition is `min` (the better of two costs), tropical multiplication is
ordinary addition of costs, the tropical `0` is `⊤` ("infinitely bad") and the tropical
`1` is the real number `0` ("neutral").

A *tropical social welfare function* on `n` voters is a map `f : TRⁿ → TR` subject to

* `IsTropLinear f` : `f x = ⨁ᵢ aᵢ ⊙ xᵢ` for some coefficient vector `a` (tropical
  linearity — this is the tropical analogue of *independence of irrelevant
  alternatives*: the aggregate is assembled coordinatewise, with no cross terms);
* `TropPareto f` : `f (c, …, c) = c` (unanimity / tropical Pareto);
* `TropScaleInv f` : `f (x ⊙ y) = f x ⊙ f y` (tropical multiplicativity: aggregating a
  sum of two cost profiles is the same as summing the two aggregates — the tropical
  analogue of *neutrality under a common change of scale*).

## Main results

* `tropical_arrow` : the three axioms force `f` to be the projection `x ↦ x k` for a
  unique voter `k` — a *tropical dictator*.
* `isTropLinear_of_tropIIA`, `tropical_arrow_of_tropIIA`, `tropical_arrow_tropIIA_iff` :
  linearity is in fact *derivable*, so the theorem holds with the weaker hypothesis
  `TropIIA` (preservation of tropical addition) in place of `IsTropLinear`.
* `tropForm_sandwich` : every unanimous tropical linear rule lies between the Rawlsian
  rule and the minimum rule of its oligarchy `{i | aᵢ = 1}`.
* `tropical_arrow_iff`, `tropicalSWF_eq_range_tropDictator` : the exact characterisation
  and the corresponding set equality; distinct voters give distinct dictators
  (`tropDictator_injective`).
* `exists_nondictatorial_of_tropPareto_tropIIA` : dropping only tropical
  multiplicativity, the "Rawlsian" rule `x ↦ ⨁ᵢ xᵢ` (the minimum cost, i.e. maximin) is
  tropically linear, satisfies tropical IIA and tropical Pareto, and is *not*
  dictatorial.  This confirms the conjecture that the weaker tropical axiom system
  admits non-dictatorial rules.
* `softMin_tendsto_inf'`, `trop_inf'_eq_tropCoalition` : the classical (zero
  temperature, Maslov dequantisation) limit.  The Boltzmann aggregator
  `-(1/t) log ∑ᵢ exp (-t yᵢ)` converges as `t → ∞` to the tropical coalition rule, and
  the tropical rule is literally the tropicalisation of that limit.
* `arrow_classical_dictatorship` : the *ordinal* rule induced by a tropical social
  welfare function ranks alternatives exactly as voter `k` does — Arrow's conclusion.
  The induced rule of a dictator satisfies classical Pareto and classical IIA
  (`dictator_classical_IIA`), while the non-dictatorial Rawlsian rule violates
  classical IIA (`rawlsian_violates_classical_IIA`), which is precisely why it escapes
  Arrow's theorem.
-/

open TropicalSocialChoice

open Finset Filter Tropical





/-! ## The axioms -/


variable {n : ℕ}








/-! ### Basic properties of tropical linear forms -/











/-! ### Tropical linearity is *derivable* from the other two axioms -/





/-! ### The dictator satisfies every axiom -/






/-- Distinct voters give distinct dictators. -/
theorem tropDictator_injective : Function.Injective (tropDictator (n := n)) := by
  classical
  intro j k h
  by_contra hjk
  have h1 : (Pi.single j (1 : TR) : Fin n → TR) j = (Pi.single j (1 : TR) : Fin n → TR) k :=
    congrFun h (Pi.single j 1)
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjk)] at h1
  exact one_ne_zero h1

/-! ## The tropical Arrow theorem -/








/-! ## Escaping the theorem: coalition (Rawlsian) rules -/


variable {n : ℕ}
















/-! ## The classical limit: Maslov dequantisation -/


variable {ι : Type*}







/-! ## Reduction to classical (ordinal) social choice -/


variable {n : ℕ} {α : Type*}










open TropicalSocialChoice in
theorem solution{f : (Fin n → TR) → TR} (hlin : IsTropLinear f) (hpar : TropPareto f)
    (hmul : TropScaleInv f) : ∃! k : Fin n, f = tropDictator k := by
  classical
  obtain ⟨a, ha⟩ := hlin
  -- some coefficient is nonzero, else `f` would be constantly `0`, contradicting unanimity
  have hex : ∃ k, a k ≠ 0 := by
    by_contra hno
    push_neg at hno
    have h1 : f (fun _ => 1) = 0 := by
      rw [ha, tropForm]
      exact Finset.sum_eq_zero fun i _ => by rw [hno i, zero_mul]
    rw [hpar 1] at h1
    exact one_ne_zero h1
  obtain ⟨k, hk⟩ := hex
  -- every other coefficient vanishes
  have hzero : ∀ j, j ≠ k → a j = 0 := by
    intro j hj
    rcases mul_eq_zero.mp (coeff_mul_coeff_eq_zero ha hmul hj) with h | h
    · exact h
    · exact absurd h hk
  -- hence `f x = a k ⊙ x k`
  have hfx : ∀ x, f x = a k * x k := by
    intro x
    rw [ha, tropForm, Finset.sum_eq_single k]
    · intro b _ hb; rw [hzero b hb, zero_mul]
    · intro h; simp at h
  -- unanimity pins down `a k = 1`
  have hak : a k = 1 := by
    have := hpar 1
    rw [hfx] at this
    simpa using this
  refine ⟨k, ?_, ?_⟩
  · funext x
    rw [hfx, hak, one_mul]
    rfl
  · intro j hj
    apply tropDictator_injective
    rw [← hj]
    funext x
    rw [hfx, hak, one_mul]
    rfl
