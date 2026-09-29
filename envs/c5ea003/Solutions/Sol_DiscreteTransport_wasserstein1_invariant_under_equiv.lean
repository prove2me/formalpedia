-- Prove2me | solution 1 for DiscreteTransport.wasserstein1_invariant_under_equiv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:35:15.235993+00:00
-- url     : https://prove2.me/submissions/eab5cc2c-b500-43db-bf21-c8a56fce8d41

-- Sol generated from Bridges/TransportTropical/WassersteinInvariance.lean
import Mathlib
import Definitions.Def_Bridges_TransportTropical_WassersteinInvariance
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wasserstein Distance Invariance Under Cost-Preserving Bijections

This file formalizes a discrete Wasserstein-1 distance on finite probability vectors
over `Fin n`, and proves that it is invariant under cost-preserving bijections
(permutations). This is the foundational theorem establishing that Wasserstein
geometry is intrinsic to the cost structure, not to labels.

## Main results

- `IsProbVec`: Predicate for probability vectors (nonneg, sum to 1)
- `transportPlans`: Set of admissible transport plans with marginal constraints
- `transportCost`: Linear cost of a transport plan
- `wasserstein1`: Discrete Wasserstein-1 distance as infimum over transport costs
- `pushforwardEquiv`: Pushforward of a distribution by a bijection
- `reindexPlan`: Reindexing a transport plan by an equivalence
- `reindexPlan_mem_transportPlans`: Reindexed plans remain admissible
- `reindexPlan_cost_eq`: Reindexed plans have equal cost under cost-preserving bijections
- `wasserstein1_invariant_under_equiv`: **The flagship theorem** — Wasserstein distance
  is invariant under cost-preserving bijections

## Mathematical significance

This theorem shows that the Wasserstein metric depends only on the cost geometry,
not on the labeling of points. It is the seed for equivariant optimal transport,
orbit reduction, and transport on quotient spaces.
-/

open Finset BigOperators

open DiscreteTransport

variable {n : ℕ}







/-- Reindexing preserves nonnegativity. -/
theorem reindexPlan_nonneg (e : Fin n ≃ Fin n) (π : Fin n → Fin n → ℝ)
    (hπ : ∀ i j, 0 ≤ π i j) :
    ∀ i j, 0 ≤ reindexPlan e π i j := by
  intro i j
  exact hπ _ _

/-
Reindexing preserves row marginals (they become the pushforward).
-/
theorem reindexPlan_row_sum (e : Fin n ≃ Fin n) (π : Fin n → Fin n → ℝ)
    (μ : Fin n → ℝ) (hrow : ∀ i, ∑ j, π i j = μ i) (i : Fin n) :
    ∑ j, reindexPlan e π i j = pushforwardEquiv e μ i := by
  -- By changing the variables of summation using the bijection $e.symm$, we can rewrite the sum.
  have h_sum_change : ∑ j, π (e.symm i) (e.symm j) = ∑ j', π (e.symm i) j' := by
    conv_rhs => rw [ ← Equiv.sum_comp e.symm ] ;
  exact h_sum_change.trans ( hrow _ )

/-
Reindexing preserves column marginals (they become the pushforward).
-/
theorem reindexPlan_col_sum (e : Fin n ≃ Fin n) (π : Fin n → Fin n → ℝ)
    (ν : Fin n → ℝ) (hcol : ∀ j, ∑ i, π i j = ν j) (j : Fin n) :
    ∑ i, reindexPlan e π i j = pushforwardEquiv e ν j := by
  unfold reindexPlan pushforwardEquiv;
  rw [ ← hcol, Equiv.sum_comp e.symm fun i => π i ( e.symm j ) ]

/-- Reindexed plans are admissible for pushforward marginals. -/
theorem reindexPlan_mem_transportPlans (e : Fin n ≃ Fin n) (π : Fin n → Fin n → ℝ)
    (μ ν : Fin n → ℝ) (hπ : π ∈ transportPlans μ ν) :
    reindexPlan e π ∈ transportPlans (pushforwardEquiv e μ) (pushforwardEquiv e ν) := by
  obtain ⟨hnn, hrow, hcol⟩ := hπ
  exact ⟨reindexPlan_nonneg e π hnn,
         fun i => reindexPlan_row_sum e π μ hrow i,
         fun j => reindexPlan_col_sum e π ν hcol j⟩

/-
The inverse reindexing recovers the original plan.
-/

/-
Reindexing by equivalence is a bijection on transport plans.
-/

/-
Transport cost is preserved under cost-preserving reindexing.
-/
theorem reindexPlan_cost_eq (e : Fin n ≃ Fin n) (c : Fin n → Fin n → ℝ)
    (π : Fin n → Fin n → ℝ) (hc : ∀ i j, c (e i) (e j) = c i j) :
    transportCost c (reindexPlan e π) = transportCost c π := by
  -- By definition of reindexPlan, we can rewrite the transport cost as:
  have h_reindex : ∑ i, ∑ j, reindexPlan e π i j * c i j = ∑ i, ∑ j, π i j * c (e i) (e j) := by
    simp +decide only [reindexPlan];
    conv_rhs => rw [ ← Equiv.sum_comp e.symm ] ;
    exact Finset.sum_congr rfl fun i hi => by rw [ ← Equiv.sum_comp e ] ; simp +decide [ hc ] ;
  unfold transportCost; aesop

/-
**Flagship theorem**: The Wasserstein-1 distance is invariant under
    cost-preserving bijections.

    If `e : Fin n ≃ Fin n` preserves costs (`c(e(x), e(y)) = c(x,y)`)
    then `W_c(e_*μ, e_*ν) = W_c(μ, ν)`.

    This establishes that Wasserstein geometry is intrinsic to the cost
    structure and independent of labeling.
-/


open DiscreteTransport in
theorem solution    (c : Fin n → Fin n → ℝ) (μ ν : Fin n → ℝ)
    (e : Fin n ≃ Fin n)
    (hc : ∀ i j, c (e i) (e j) = c i j) :
    wasserstein1 c (pushforwardEquiv e μ) (pushforwardEquiv e ν) =
    wasserstein1 c μ ν := by
  unfold pushforwardEquiv wasserstein1;
  congr! 1;
  ext;
  constructor <;> rintro ⟨ π, hπ, rfl ⟩;
  · refine' ⟨ reindexPlan e.symm π, _, _ ⟩;
    · convert reindexPlan_mem_transportPlans e.symm π _ _ hπ using 1;
      unfold pushforwardEquiv; aesop;
    · apply reindexPlan_cost_eq;
      exact fun i j => by rw [ ← hc, e.apply_symm_apply, e.apply_symm_apply ] ;
  · use reindexPlan e π;
    exact ⟨ reindexPlan_mem_transportPlans e π μ ν hπ, reindexPlan_cost_eq e c π hc ⟩
