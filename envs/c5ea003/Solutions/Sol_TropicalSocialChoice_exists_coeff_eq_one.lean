-- Prove2me | solution 1 for TropicalSocialChoice.exists_coeff_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:58:33.546328+00:00
-- url     : https://prove2.me/submissions/8b7ee47b-276d-4389-a94d-2106706f09e1

-- Sol generated from Probability/TropicalSocialChoice.lean
import Mathlib
import Definitions.Def_Probability_TropicalSocialChoice
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







/-! ## The tropical Arrow theorem -/








/-! ## Escaping the theorem: coalition (Rawlsian) rules -/


variable {n : ℕ}
















/-! ## The classical limit: Maslov dequantisation -/


variable {ι : Type*}







/-! ## Reduction to classical (ordinal) social choice -/


variable {n : ℕ} {α : Type*}










open TropicalSocialChoice in
theorem solution{a : Fin n → TR} (h : ∑ i, a i = 1) : ∃ k, a k = 1 := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with he | hn
    · rw [he, Finset.sum_empty] at h
      exact absurd h.symm one_ne_zero
    · exact hn
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' hne (untrop ∘ a)
  refine ⟨k, ?_⟩
  have h1 : untrop (∑ i, a i) = untrop (a k) := by
    rw [Finset.untrop_sum', ← Finset.inf'_eq_inf hne, hk]; rfl
  rw [h] at h1
  exact untrop_injective h1.symm
