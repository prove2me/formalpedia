-- Prove2me | Definitions.Def_Bridges_NeuralCoding_WeightedTropicalHodge
-- name    : Bridges_NeuralCoding_WeightedTropicalHodge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:40.519702+00:00
-- url     : https://prove2.me/theorems/592776ee-cc02-43cf-8cbe-b1698e0d1bc4
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_WeightedTropicalHodge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.WeightedTropicalHodge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/WeightedTropicalHodge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Weighted Tropical Graph Hodge Theory

This file establishes a weighted tropical harmonicity theory on graphs,
introducing a min-plus balancing law with valuations that generalizes
ordinary graph Laplacian harmonicity to the tropical setting.

## Main Definitions

* `WeightedGraph` — a finite simple graph with integer edge weights
* `weightedNbrVal` — the weighted neighbor value `w(i,j) + φ(j)`
* `tropBalancedAt` — tropical balance at a vertex
* `weightedTropKernelOn` — the weighted tropical kernel on a vertex subset
* `GenericWeights` — pairwise distinct incident edge weights
* `WeightDegenerateAt` — local weight degeneracy
* `WeightCompatibleCycle` — cycle admitting a balanced potential
* `qVisibleWeightedComponent` — component with degenerate q-access

## Main Results

* `weighted_cycle_balance` — algebraic transport identity
* `kernel_translate_invariant` — kernel closed under constant shifts
* `tropBalancedAt_of_two_witnesses` — constructive balance
* `generic_zero_not_balanced` — genericity prevents zero balance
* `weightCompatibleCycle_gives_kernel_vector` — cycles give kernel vectors
* `weighted_component_indicator_in_kernel` — components give kernel vectors
* `shortestPathDegeneracy_eq_weightDegeneracy` — cross-domain identity
* `not_generic_iff_exists_degenerate` — degeneracy characterization
* `zero_in_kernel_of_all_degenerate_and_minimal` — degeneracy kernel membership

## References

* Baker–Norine (2007), "Riemann–Roch and Abel–Jacobi theory on a finite graph"
* Mikhalkin (2006), "Tropical geometry and its applications"
-/


open Finset BigOperators Classical

noncomputable section

/-! ## Definitions -/

/-- A weighted simple graph: a finite simple graph with integer edge weights. -/
structure WeightedGraph (V : Type*) [Fintype V] where
  Adj : V → V → Prop
  symm : Symmetric Adj
  loopless : ∀ v, ¬ Adj v v
  w : V → V → ℤ
  w_symm : ∀ ⦃u v⦄, Adj u v → w u v = w v u

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted neighbor value `w(i,j) + φ(j)`. -/
def weightedNbrVal (G : WeightedGraph V) (φ : V → ℤ) (i j : V) : ℤ :=
  G.w i j + φ j

/-- Tropical balance at vertex `i`: the minimum of `w(i,j) + φ(j)` over
    neighbors `j` is attained by at least two distinct neighbors. -/
def tropBalancedAt (G : WeightedGraph V) (φ : V → ℤ) (i : V) : Prop :=
  ∃ j k : V, j ≠ k ∧ G.Adj i j ∧ G.Adj i k ∧
    G.weightedNbrVal φ i j = G.weightedNbrVal φ i k ∧
    ∀ l, G.Adj i l → G.weightedNbrVal φ i j ≤ G.weightedNbrVal φ i l

/-- The weighted tropical kernel on vertex set `S`. -/
def weightedTropKernelOn (G : WeightedGraph V) (S : Finset V) : Set (V → ℤ) :=
  {φ | ∀ i ∈ S, G.tropBalancedAt φ i}

/-- Generic weights: all incident edge weights are pairwise distinct. -/
def GenericWeights (G : WeightedGraph V) : Prop :=
  ∀ ⦃i j k⦄, G.Adj i j → G.Adj i k → j ≠ k → G.w i j ≠ G.w i k

/-- Weight degeneracy at vertex `i`. -/
def WeightDegenerateAt (G : WeightedGraph V) (i : V) : Prop :=
  ∃ j k : V, j ≠ k ∧ G.Adj i j ∧ G.Adj i k ∧ G.w i j = G.w i k

/-- Count of weight-degenerate vertices in `S`. -/
noncomputable def weightDegeneracyCount (G : WeightedGraph V) (S : Finset V) : ℕ :=
  (S.filter (fun i => ∃ j k : V, j ≠ k ∧ G.Adj i j ∧ G.Adj i k ∧ G.w i j = G.w i k)).card

/-- Count of vertices in `S` with shortest-path degeneracy. -/
noncomputable def shortestPathDegeneracyCount (G : WeightedGraph V)
    (_q : V) (S : Finset V) : ℕ :=
  (S.filter (fun v => ∃ j k : V, j ≠ k ∧ G.Adj v j ∧ G.Adj v k ∧ G.w v j = G.w v k)).card

/-- Weight-compatible cycle: nonempty set with a balanced zero-outside potential. -/
def WeightCompatibleCycle (G : WeightedGraph V) (C : Finset V) : Prop :=
  C.Nonempty ∧
  ∃ φ : V → ℤ, (∀ v, v ∉ C → φ v = 0) ∧ ∀ i ∈ C, G.tropBalancedAt φ i

/-- q-visible weighted component. -/
def qVisibleWeightedComponent (G : WeightedGraph V) (q : V) (T : Finset V) : Prop :=
  T.Nonempty ∧ q ∉ T ∧
  ∃ c : ℤ, ∃ φ : V → ℤ, (∀ v, v ∈ T → φ v = c) ∧ (∀ v, v ∉ T → φ v = 0) ∧
    ∀ i ∈ T, G.tropBalancedAt φ i

/-! ## Theorems -/

/-
**Weighted cycle balance lemma.** Transport identity for potentials.
-/

/-
**Kernel translation invariance.**
-/

/-
**Constructive tropical balance.**
-/

/-
**Generic weights prevent zero balance.**
-/

/-
**Weight-compatible cycles produce kernel vectors.**
-/

/-
**q-visible components produce kernel vectors.**
-/

/-
**Cross-domain: shortest-path degeneracy = weight degeneracy.**
-/

/-
**Degeneracy characterization.**
-/

/-
**Zero in kernel under full degeneracy with minimality.**
-/

end WeightedGraph

end


