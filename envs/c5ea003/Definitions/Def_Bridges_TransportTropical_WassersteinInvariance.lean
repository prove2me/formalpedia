-- Prove2me | Definitions.Def_Bridges_TransportTropical_WassersteinInvariance
-- name    : Bridges_TransportTropical_WassersteinInvariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:03.175288+00:00
-- url     : https://prove2.me/theorems/a31a950c-73e5-46a6-b811-8129ded3e077
-- title:
--   Aether Catalog definitions — Bridges_TransportTropical_WassersteinInvariance
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TransportTropical.WassersteinInvariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TransportTropical/WassersteinInvariance.lean by skeleton subtraction
import Mathlib
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

namespace DiscreteTransport

variable {n : ℕ}


/-- The set of transport plans between two marginals μ and ν.
    A transport plan π is a nonneg matrix whose row sums equal μ and column sums equal ν. -/
def transportPlans (μ ν : Fin n → ℝ) : Set (Fin n → Fin n → ℝ) :=
  {π | (∀ i j, 0 ≤ π i j) ∧
       (∀ i, ∑ j, π i j = μ i) ∧
       (∀ j, ∑ i, π i j = ν j)}

/-- The transport cost of a plan π under cost function c. -/
def transportCost (c : Fin n → Fin n → ℝ) (π : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, π i j * c i j

/-- The discrete Wasserstein-1 distance: infimum of transport costs over all plans. -/
noncomputable def wasserstein1 (c : Fin n → Fin n → ℝ) (μ ν : Fin n → ℝ) : ℝ :=
  sInf (transportCost c '' transportPlans μ ν)

/-- Pushforward of a distribution by an equivalence. -/
def pushforwardEquiv (e : Fin n ≃ Fin n) (μ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => μ (e.symm i)

/-- Reindex a transport plan by an equivalence:
    π'(i,j) = π(e⁻¹(i), e⁻¹(j)). -/
def reindexPlan (e : Fin n ≃ Fin n) (π : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => π (e.symm i) (e.symm j)


/-
Reindexing preserves row marginals (they become the pushforward).
-/

/-
Reindexing preserves column marginals (they become the pushforward).
-/


/-
The inverse reindexing recovers the original plan.
-/

/-
Reindexing by equivalence is a bijection on transport plans.
-/

/-
Transport cost is preserved under cost-preserving reindexing.
-/

/-
**Flagship theorem**: The Wasserstein-1 distance is invariant under
    cost-preserving bijections.

    If `e : Fin n ≃ Fin n` preserves costs (`c(e(x), e(y)) = c(x,y)`)
    then `W_c(e_*μ, e_*ν) = W_c(μ, ν)`.

    This establishes that Wasserstein geometry is intrinsic to the cost
    structure and independent of labeling.
-/

end DiscreteTransport


