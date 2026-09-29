-- Prove2me | Theorems.Thm_TropicalBarronChoquet_sup_p_erase_of_dominated_p
-- name    : TropicalBarronChoquet.sup_p_erase_of_dominated_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T23:34:20.685419+00:00
-- url     : https://prove2.me/theorems/e2ddf659-3f09-4785-8e4b-69acf59f04d2
-- title:
--   The sup over `S` equals the sup over `S.erase i` when `i`'s value is dominated.
-- statement:
--   The sup over `S` equals the sup over `S.erase i` when `i`'s value is dominated.
--
--   ```lean
--   theorem TropicalBarronChoquet.sup'_erase_of_dominated'(S : Finset 𝓕) (hS : S.Nonempty) (g : 𝓕 → ℝ)
--       (i : 𝓕) (hi : i ∈ S) (hS' : (S.erase i).Nonempty)
--       (hdom : ∃ j ∈ S, j ≠ i ∧ g i ≤ g j) :
--       S.sup' hS g = (S.erase i).sup' hS' g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalBarronChoquetDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalBarronChoquetDuality.lean#L128

-- Thm stub generated from Bridges/TropicalBarronChoquetDuality.lean
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

theorem TropicalBarronChoquet.sup_p_erase_of_dominated_p(S : Finset 𝓕) (hS : S.Nonempty) (g : 𝓕 → ℝ)
    (i : 𝓕) (hi : i ∈ S) (hS' : (S.erase i).Nonempty)
    (hdom : ∃ j ∈ S, j ≠ i ∧ g i ≤ g j) :
    S.sup' hS g = (S.erase i).sup' hS' g := by sorry
