-- Prove2me | solution 1 for BonferroniMarginals.card_filter_superset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:23:52.819395+00:00
-- url     : https://prove2.me/submissions/41c5f7d9-9256-4f6f-b055-4cd519360dac

-- Sol generated from MachineLearning/BonferroniMarginals/HigherOrderNecessity.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
import Definitions.Def_MachineLearning_BonferroniMarginals_MarginalIndeterminacy

/-!
# Every marginal order below `k` is insufficient for `k` sets

`MarginalIndeterminacy.lean` exhibits three sets whose first- and second-order
marginals coincide but whose unions differ, showing that the Bonferroni
machinery can never be upgraded to an identity.  That example leaves open the
obvious escape route: *maybe order `3`, or order `17`, always suffices.*

This file closes the escape route completely.  For **every** `k ≥ 1` we build
two families of `k` sets, `plainFam k` and `parityFam k`, on a common ground set
of `2^(k+1)` points such that

* all joint marginals of order `< k` agree —
  `jointFail_card_eq_of_ne_univ`: `|⋂_{i ∈ T} Aᵢ| = |⋂_{i ∈ T} Bᵢ|` for every
  `T ≠ univ`;
* the top-order marginal differs (`jointFail_card_univ_ne`), and
* the unions differ (`card_cover_ne`), one being odd and the other even.

Hence `marginal_order_lt_insufficient`: no functional of the marginals of order
`< k` can compute the union of `k` sets, for any `k ≥ 1`.  Together with
`card_cover_eq_of_all_inf_card_eq` (inclusion–exclusion), the marginal order
threshold for a family of `k` sets is **exactly `k`**.

## The construction

Ground set `Ω = Finset (Fin k) × Bool`: two labelled copies of every subset of
`Fin k`.

* `plainFam k i = {(S, false) | i ∈ S}` — one copy of each subset containing `i`.
* `parityFam k i = {(S, b) | i ∈ S, |S| ≡ k (mod 2)}` — *two* copies of the
  subsets of the correct size parity.

Writing `w(S)` for the number of ground points sitting over `S`, the two
families have weight functions `1` and `1 + (−1)^{k−|S|}`; the perturbation
`δ(S) = (−1)^{k−|S|}` has vanishing "upper sums" `∑_{S ⊇ T} δ(S) = 0` for all
`T ≠ univ`, by the alternating binomial identity — and this is exactly the
statement that all marginals of order `< k` are unchanged.  The perturbation is
invisible below order `k` and flips the parity of the union.
-/

open BonferroniMarginals

open Finset

/-! ## Joint marginals of arbitrary order -/


/-! ## Counting subsets with a prescribed size parity -/


/-! ## Supersets of a fixed set -/

variable {k : ℕ}




/-! ## The two families -/







/-! ## The unions differ -/




/-! ## The main theorem -/




open BonferroniMarginals in
theorem solution(T : Finset (Fin k)) (P : ℕ → Prop) [DecidablePred P] :
    ((univ : Finset (Finset (Fin k))).filter (fun S => T ⊆ S ∧ P S.card)).card
      = ((Tᶜ).powerset.filter (fun U => P (U.card + T.card))).card := by
  classical
  refine Finset.card_nbij' (fun S => S \ T) (fun U => U ∪ T) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS
    obtain ⟨hTS, hPS⟩ := hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_sdiff] at hx
      simpa [Finset.mem_compl] using hx.2
    · rwa [Finset.card_sdiff_add_card_eq_card hTS]
  · intro U hU
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hU
    obtain ⟨hUT, hPU⟩ := hU
    have hdisj : Disjoint U T := by
      rw [Finset.disjoint_right]
      intro x hxT hxU
      have := hUT hxU
      simp only [Finset.mem_compl] at this
      exact this hxT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact ⟨Finset.subset_union_right, by rwa [Finset.card_union_of_disjoint hdisj]⟩
  · intro S hS
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS
    exact Finset.sdiff_union_of_subset hS.1
  · intro U hU
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hU
    have hdisj : Disjoint U T := by
      rw [Finset.disjoint_right]
      intro x hxT hxU
      have := hU.1 hxU
      simp only [Finset.mem_compl] at this
      exact this hxT
    show (U ∪ T) \ T = U
    rw [Finset.union_sdiff_cancel_right hdisj]
