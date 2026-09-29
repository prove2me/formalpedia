-- Prove2me | Definitions.Def_Bridges_TransportTropical_PermutationCouplings
-- name    : Bridges_TransportTropical_PermutationCouplings
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:00.313282+00:00
-- url     : https://prove2.me/theorems/31d471fd-d7c5-486f-a3ba-04758717db06
-- title:
--   Aether Catalog definitions — Bridges_TransportTropical_PermutationCouplings
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TransportTropical.PermutationCouplings`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TransportTropical/PermutationCouplings.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Permutation Couplings: Bridge between Transport and Tropical Optimization

This file connects optimal transport with tropical/combinatorial optimization
by studying permutation couplings — transport plans induced by permutations
between uniform distributions.

## Main definitions
- `uniformProb n`: the uniform probability vector on `Fin n`
- `permPlan σ`: the transport plan induced by a permutation σ

## Main results
- `permPlan_is_transportPlan`: permutation plans are valid transport plans
    between uniform distributions
- `permPlan_transportCost`: the transport cost of a permutation plan equals
    the assignment cost `(1/n) ∑ᵢ c(i, σ(i))`
- `permPlan_cost_conjugation_invariant`: simultaneous relabeling by a bijection
    preserves the assignment cost, connecting group-theoretic symmetry
    to tropical optimization invariance
-/

open Finset BigOperators

variable {n : ℕ}

/-- The uniform probability vector on `Fin n`. -/
noncomputable def uniformProb (n : ℕ) : Fin n → ℝ := fun _ => (n : ℝ)⁻¹

/-- The transport plan induced by a permutation σ: mass (1/n) is placed at (i, σ(i)). -/
noncomputable def permPlan (σ : Fin n ≃ Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if σ i = j then (n : ℝ)⁻¹ else 0

/-- The set of transport plans from μ to ν (reproduced for self-containment). -/
def transportPlans' (μ ν : Fin n → ℝ) : Set (Fin n → Fin n → ℝ) :=
  {π | (∀ i j, 0 ≤ π i j) ∧
       (∀ i, ∑ j, π i j = μ i) ∧
       (∀ j, ∑ i, π i j = ν j)}

/-- The transport cost of plan π under cost c. -/
def transportCost' (c : Fin n → Fin n → ℝ) (π : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, π i j * c i j

/-! ## Permutation plans are valid transport plans -/

/-
Permutation plans have nonneg entries.
-/

/-
Permutation plans have correct row sums (each equals 1/n).
-/

/-
Permutation plans have correct column sums (each equals 1/n).
-/

/-
**A permutation plan is a valid transport plan between uniform distributions.**
-/

/-! ## Transport cost of permutation plans -/

/-
The transport cost of a permutation plan equals the scaled assignment cost.
-/

/-! ## Conjugation invariance of assignment cost -/

/-
**Assignment cost is invariant under conjugation by a cost-preserving bijection.**

    If `e` preserves the cost function (`c (e i) (e j) = c i j`), then
    conjugating a permutation σ by e (i.e., replacing σ with e ∘ σ ∘ e⁻¹)
    does not change the assignment cost.

    This is the bridge theorem: it connects the group-theoretic notion
    of conjugation to the transport-theoretic notion of relabeling invariance,
    and to the tropical-algebraic notion that min-plus optimization
    over assignments is invariant under simultaneous reindexing.
-/


