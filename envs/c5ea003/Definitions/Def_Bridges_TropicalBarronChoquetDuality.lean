-- Prove2me | Definitions.Def_Bridges_TropicalBarronChoquetDuality
-- name    : Bridges_TropicalBarronChoquetDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:54.979811+00:00
-- url     : https://prove2.me/theorems/73ad0118-d004-4301-9dd8-31b00e0adc49
-- title:
--   Aether Catalog definitions — Bridges_TropicalBarronChoquetDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalBarronChoquetDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalBarronChoquetDuality.lean by skeleton subtraction
import Mathlib
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

namespace TropicalBarronChoquet

variable {𝓕 F : Type*} [DecidableEq 𝓕]

/-! ## §1. Tropical Network Representations -/

/-- A **tropical network representation** consists of a finite support set,
    weight function, and evaluation functionals. It computes:
    `N(f) = max_{i ∈ support} (weight(i) + eval(i)(f))` -/
structure TropicalNetworkRep (𝓕 F : Type*) where
  /-- The finite support set of active hidden units -/
  support : Finset 𝓕
  /-- The weight assigned to each hidden unit -/
  weight : 𝓕 → ℝ
  /-- The evaluation functional for each hidden unit -/
  eval : 𝓕 → F → ℝ

variable {R R₁ R₂ : TropicalNetworkRep 𝓕 F}

/-- The function computed by a tropical network. When support is empty, returns 0. -/
def TropicalNetworkRep.realize (R : TropicalNetworkRep 𝓕 F) (f : F) : ℝ :=
  if h : R.support.Nonempty then
    R.support.sup' h (fun i => R.weight i + R.eval i f)
  else 0



/-! ## §2. Dominance and Irredundancy -/




/-! ## §3. Separating Evaluations -/

/-- Evaluation functionals **separate** if distinct indices have distinct evaluation
    profiles. -/
def SeparatingEvals (eval : 𝓕 → F → ℝ) : Prop :=
  ∀ i j : 𝓕, i ≠ j → ∃ f : F, eval i f ≠ eval j f

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


end TropicalBarronChoquet


