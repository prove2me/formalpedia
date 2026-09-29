-- Prove2me | solution 1 for TropicalBarronChoquet.sup_p_erase_of_dominated_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:35:55.06473+00:00
-- url     : https://prove2.me/submissions/a61cc6ac-db7d-4061-a960-e4071dac60f4

-- Sol generated from Bridges/TropicalBarronChoquetDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalBarronChoquetDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Barron–Choquet Duality via Idempotent Feature Semimodules

This file formalizes a **finite representation and reconstruction theorem** that connects
abstract tropical Choquet functionals to canonical sparse shallow tropical networks.

## Mathematical Context

In max-plus (tropical) algebra, "addition" is `max` and "multiplication" is `+`.
A **tropical network** with support `I ⊆ 𝓕` and weights `w : 𝓕 → ℝ` computes:

  `N(f) = max_{i ∈ I} (w(i) + eval(i)(f))`

where `eval : 𝓕 → (F → ℝ)` is a family of evaluation functionals (feature maps).

The **Tropical Barron–Choquet Duality** says:
1. Every sup-preserving, shift-equivariant functional admits such a representation.
2. Dominated hidden units can be pruned without changing the functional.
3. The irredundant (pruned) representation has minimum support cardinality.
4. Under a separation hypothesis, the irredundant support set is unique.

## Main Definitions

* `TropicalNetworkRep` — A tropical network representation (support, weights, evaluations)
* `TropicalNetworkRep.realize` — The function computed by a network
* `IsDominated` — A hidden unit is dominated if it never achieves the maximum
* `IsIrredundant` — A representation where no unit is dominated
* `SeparatingEvals` — Evaluation functionals that separate distinct indices

## Main Results

* `realize_erase_of_pointwise_dominated` — Removing a dominated unit preserves the functional
* `realize_sup_preserving` — Network realizations preserve tropical addition (max)
* `realize_shift_equivariant` — Network realizations are shift-equivariant
* `realize_monotone` — Network realizations are monotone
* `irredundant_support_card_eq` — Irredundant representations have equal support cardinality
* `certified_compression_of_dominated` — Dominated units can be certified-removed
* `network_weight_stability` — Weight perturbation stability bound
* `sparse_reconstruction` — Weights recovered from isolating test inputs

## Cross-Domain Connections

- **Tropical convex geometry**: extremal rays, tropical Carathéodory
- **Functional analysis**: Choquet-style representation, representer theorems
- **Machine learning**: sparse shallow networks, width minimization, certified compression
- **Idempotent analysis**: sup-preserving maps, max-plus linearity

## Application Keywords

`tropical neural networks`, `idempotent functional analysis`, `Choquet duality`,
`Barron space`, `sparse reconstruction`, `network compression`, `max-plus algebra`,
`extremal rays`, `certified recovery`, `interpretable ML`, `atomic decomposition`,
`minimal width realization`
-/

noncomputable section

open Finset

open TropicalBarronChoquet

variable {𝓕 F : Type*} [DecidableEq 𝓕]

/-! ## §1. Tropical Network Representations -/


variable {R R₁ R₂ : TropicalNetworkRep 𝓕 F}




/-! ## §2. Dominance and Irredundancy -/




/-! ## §3. Separating Evaluations -/


/-! ## §4. Core Finset Sup Lemmas -/





/-! ## §5. Dominated Unit Elimination -/


/-! ## §6. Network Axiom Theorems -/




/-! ## §7. Tropical Max Idempotent -/



/-! ## §8. Certified Compression -/

/-
**Certified neural compression via tropical dominance.**
    A dominated unit can be removed, strictly reducing support cardinality.
-/

/-! ## §9. Weight Perturbation Stability -/

/-
**Weight perturbation bound.** Close networks have close weights.
-/

/-! ## §10. Sparse Reconstruction -/

/-
**Sparse reconstruction theorem.** Weights can be recovered from isolating inputs.
-/

/-! ## §11. Irredundant Support Cardinality -/

/-
**Irredundant support is cardinality-minimal.**
    Given an injective covering from the irredundant support `I` into `J`,
    we have `|I| ≤ |J|`.
-/


/-! ## §12. Certified Tropical Network Axioms Bundle -/



open TropicalBarronChoquet in
theorem solution(S : Finset 𝓕) (hS : S.Nonempty) (g : 𝓕 → ℝ)
    (i : 𝓕) (hi : i ∈ S) (hS' : (S.erase i).Nonempty)
    (hdom : ∃ j ∈ S, j ≠ i ∧ g i ≤ g j) :
    S.sup' hS g = (S.erase i).sup' hS' g := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro b hb
    by_cases hbi : b = i
    · subst hbi
      obtain ⟨j, hj, hji, hle⟩ := hdom
      exact le_trans hle (Finset.le_sup' g (Finset.mem_erase.mpr ⟨hji, hj⟩))
    · exact Finset.le_sup' g (Finset.mem_erase.mpr ⟨hbi, hb⟩)
  · apply Finset.sup'_le
    intro b hb
    exact Finset.le_sup' g (Finset.mem_of_mem_erase hb)
