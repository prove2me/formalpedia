-- Prove2me | Theorems.Thm_DiscreteTransport_wasserstein1_invariant_under_equiv
-- name    : DiscreteTransport.wasserstein1_invariant_under_equiv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:46:49.595968+00:00
-- url     : https://prove2.me/theorems/b2597ed2-14f2-47f4-ad13-9208051a62a4
-- title:
--   Wasserstein1 invariant under equiv
-- statement:
--   Formal statement of `DiscreteTransport.wasserstein1_invariant_under_equiv` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem DiscreteTransport.wasserstein1_invariant_under_equiv    (c : Fin n → Fin n → ℝ) (μ ν : Fin n → ℝ)
--       (e : Fin n ≃ Fin n)
--       (hc : ∀ i j, c (e i) (e j) = c i j) :
--       wasserstein1 c (pushforwardEquiv e μ) (pushforwardEquiv e ν) =
--       wasserstein1 c μ ν := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TransportTropical/WassersteinInvariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TransportTropical/WassersteinInvariance.lean#L150

-- Thm stub generated from Bridges/TransportTropical/WassersteinInvariance.lean
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

theorem DiscreteTransport.wasserstein1_invariant_under_equiv    (c : Fin n → Fin n → ℝ) (μ ν : Fin n → ℝ)
    (e : Fin n ≃ Fin n)
    (hc : ∀ i j, c (e i) (e j) = c i j) :
    wasserstein1 c (pushforwardEquiv e μ) (pushforwardEquiv e ν) =
    wasserstein1 c μ ν := by sorry
