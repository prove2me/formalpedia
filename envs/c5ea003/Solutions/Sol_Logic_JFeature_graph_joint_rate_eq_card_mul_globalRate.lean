-- Prove2me | solution 1 for Logic.JFeature.graph_joint_rate_eq_card_mul_globalRate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:11:54.464823+00:00
-- url     : https://prove2.me/submissions/6fc5a79d-8834-4e5b-97b3-c6b15338ddb3

-- Sol generated from Logic/JFeatureMarginalBlindness.lean
import Mathlib
import Definitions.Def_Logic_JFeatureMarginalBlindness
import Theorems.Thm_Logic_JFeature_graphFinset_rowBalanced
/-
# Marginal blindness: why no `j`-feature can carry a hidden pair-carrier

This file formalises the structural reason behind the empirical verdict
`H0_CARRIER_OPEN` of the j-feature sweep (paper 248): *eight* registered
families of arithmetic features of the position index `j`
(`j mod 4`, `j mod 3`, `j mod 5`, `j mod 7`, `j mod 105`, `omega_small(j)`
terciles, smoothness of `|j - nearest square|`, `10^6`-smoothness of `j`)
all returned honest enrichment ratios `R ≤ 1.11`.

The theorems below say that this is not an accident of the particular eight
features chosen: on a sample space `α × β` where the hit set is *row balanced*
(every value of the first coordinate carries the same number of hits), **every**
cell cut out by **any** function of the first coordinate has enrichment ratio
*exactly* `1`.  Whatever new feature of `j` one invents, the marginal sweep is
guaranteed to return `R = 1`; the sweep has no power at all against carriers
that live in the *joint* (consecutive-position) structure.

Yet such carriers exist and are arbitrarily strong: for the graph of a
permutation `σ : α ≃ β` (a row-balanced hit set with one hit per row) the joint
cell "the graph itself" has hit rate `1`, i.e. enrichment `card α` over the
global rate, while all marginal cells sit at exactly `1`.

Main results.

* `exists_fiber_hits_ge` / `exists_fiber_rate_ge_globalRate` : the *selection
  floor*.  For every feature map and every hit set there is always a nonempty
  cell whose hit rate is at least the global rate; a raw "max over cells of
  `R`" statistic is therefore `≥ 1` by pure pigeonhole, with no signal
  whatsoever.  (Used in `Logic.JFeatureMaxStatistic` to show that the
  uncalibrated max test has type-I error rate `1`.)
* `rate_rowSet`, `enrich_rowSet_eq_one`, `enrich_marginal_feature_eq_one` :
  **marginal blindness**.
* `graphFinset_rowBalanced`, `rate_graphFinset`,
  `graph_joint_rate_eq_card_mul_globalRate`,
  `marginal_blind_carrier` : the joint carrier that is invisible to every
  marginal feature, with unbounded joint enrichment.
-/

open Logic.JFeature

open Finset

/-! ## Hit rates, global rate, enrichment -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]










/-! ## The selection floor: some cell always looks enriched -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]





/-! ## Marginal blindness on a product sample space -/


variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]














/-! ### A carrier that hides from every marginal feature -/



lemma card_graphFinset (σ : α ≃ β) : (graphFinset σ).card = Fintype.card α := by
  classical
  have hmem : ∀ x ∈ graphFinset σ, x.1 ∈ (univ : Finset α) := fun x _ => Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  have h : ∀ a ∈ (univ : Finset α), ((graphFinset σ).filter (fun x => x.1 = a)).card = 1 :=
    fun a _ => graphFinset_rowBalanced σ a
  rw [Finset.sum_congr rfl h]
  simp

/-- The joint cell given by the graph itself is a perfect carrier: hit rate `1`. -/
theorem rate_graphFinset (σ : α ≃ β) (hcard : 0 < Fintype.card α) :
    rate (graphFinset σ) (graphFinset σ) = 1 := by
  have h : (0:ℝ) < ((graphFinset σ).card : ℝ) := by
    rw [card_graphFinset]; exact_mod_cast hcard
  rw [rate, Finset.inter_self]
  exact div_self (ne_of_gt h)





open Logic.JFeature in
theorem solution(σ : α ≃ β) (hcard : 0 < Fintype.card α) :
    rate (graphFinset σ) (graphFinset σ)
      = (Fintype.card β : ℝ) * globalRate (graphFinset σ) := by
  have hA : (0:ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hcard
  have hB : (0:ℝ) < (Fintype.card β : ℝ) := by
    have hc : Fintype.card β = Fintype.card α := (Fintype.card_congr σ).symm
    rw [hc]; exact hA
  rw [rate_graphFinset σ hcard, globalRate, card_graphFinset, Fintype.card_prod]
  push_cast
  field_simp
