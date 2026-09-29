-- Prove2me | Definitions.Def_Bridges_TropicalAttentionRealizationDuality
-- name    : Bridges_TropicalAttentionRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:53.693183+00:00
-- url     : https://prove2.me/theorems/e944e30f-8102-4fd8-a994-2ae4f65f48f9
-- title:
--   Aether Catalog definitions — Bridges_TropicalAttentionRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAttentionRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAttentionRealizationDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Attention Realization Duality via Idempotent Transport Semimodules

This file establishes a **finite duality/reconstruction theory** for tropical attention
mechanisms. A tropical attention layer is shown to be recoverable from semimodule-theoretic
invariants exactly when its geometry is separated enough to make sparse heads algebraically
visible.

## Mathematical Setting

We work in a finite min-plus setting. Let `I, J` be finite types. A **tropical attention
kernel** is a function `K : I → J → ℝ`, interpreted as a cost matrix. A **multi-head
tropical attention architecture** with `n` heads is a family of kernels
`heads : Fin n → (I → J → ℝ)`. The **combined kernel** is the pointwise infimum:

  `combined i j = ⨅ h, heads h i j`

The **transport semimodule** captures the essential algebraic structure of this
decomposition via irredundant generators.

## Main Results

### Realization Duality
* `roundtrip_transport_combined` — Semimodule → attention preserves combined kernel
* `roundtrip_attention_combined` — Attention → semimodule → attention round-trip
* `attentionToTransport_injective` — Injective on separated architectures

### Minimality = Head Rank
* `separated_implies_irredundant` — Separated architectures are irredundant
* `essential_head_in_subfamily` — Essential heads must appear in any sub-decomposition
* `irredundant_head_count_minimal` — Irredundant head count is minimal

### Stability
* `perturbation_preserves_separation` — Small perturbations preserve separation
* `head_count_locally_constant` — Head count stable under perturbation

### Certified Reconstruction
* `reconstruction_correct` — Reconstruction recovers a valid architecture
* `reconstruction_separated` — Reconstructed architecture is separated
-/

noncomputable section

namespace TropicalAttention

variable {I J : Type*} [Fintype I] [Fintype J]

/-! ## §1. Tropical Attention Data -/

/-- A **multi-head tropical attention architecture** with `n` heads over token types
    `I` (source) and `J` (target). -/
structure MultiHeadAttn (I J : Type*) (n : ℕ) where
  /-- The kernel for each attention head -/
  heads : Fin n → I → J → ℝ

/-- The **combined kernel**: pointwise infimum over heads. -/
def MultiHeadAttn.combined {n : ℕ} (A : MultiHeadAttn I J n) (i : I) (j : J) : ℝ :=
  ⨅ h : Fin n, A.heads h i j


/-! ## §2. Dominance, Irredundancy, Separation -/

/-- Head `h` is **dominated** if at every point, some other head achieves ≤ value. -/
def IsDominated {n : ℕ} (A : MultiHeadAttn I J n) (h : Fin n) : Prop :=
  ∀ i : I, ∀ j : J, ∃ k : Fin n, k ≠ h ∧ A.heads k i j ≤ A.heads h i j

/-- An architecture is **irredundant** if no head is dominated. -/
def IsIrredundant {n : ℕ} (A : MultiHeadAttn I J n) : Prop :=
  ∀ h : Fin n, ¬IsDominated A h

/-- Head `h` is **essential** if it is strictly the best head at some point. -/
def IsEssential {n : ℕ} (A : MultiHeadAttn I J n) (h : Fin n) : Prop :=
  ∃ i : I, ∃ j : J, ∀ k : Fin n, k ≠ h → A.heads h i j < A.heads k i j

/-- An architecture is **separated** if every head is essential. -/
def IsSeparated {n : ℕ} (A : MultiHeadAttn I J n) : Prop :=
  ∀ h : Fin n, IsEssential A h

/-- **Quantitative separation**: each head is the unique minimum with gap ≥ δ. -/
def IsSeparatedBy {n : ℕ} (A : MultiHeadAttn I J n) (δ : ℝ) : Prop :=
  ∀ h : Fin n, ∃ i : I, ∃ j : J, ∀ k : Fin n, k ≠ h →
    A.heads h i j + δ ≤ A.heads k i j


/-! ## §3. Transport Semimodule -/

/-- An **idempotent transport semimodule**: the canonical irredundant presentation
    of a multi-head tropical attention architecture. -/
structure TransportSemimod (I J : Type*) [Fintype I] [Fintype J] where
  /-- Number of extremal generators (= rank) -/
  rank : ℕ
  /-- The extremal generator kernels -/
  generators : Fin rank → I → J → ℝ
  /-- The combined kernel -/
  combined : I → J → ℝ
  /-- Combined = pointwise inf of generators -/
  combined_spec : ∀ i j, combined i j = ⨅ k : Fin rank, generators k i j
  /-- Every generator is essential -/
  generators_essential : ∀ h : Fin rank,
    ∃ i : I, ∃ j : J, ∀ k : Fin rank, k ≠ h → generators h i j < generators k i j

/-- A transport semimodule is **finitely presented** (always true here). -/
def TransportSemimod.FinitelyPresented (_ : TransportSemimod I J) : Prop := True

/-- A transport semimodule is **separated**. -/
def TransportSemimod.Separated (M : TransportSemimod I J) : Prop :=
  ∀ h : Fin M.rank, ∃ i : I, ∃ j : J, ∀ k : Fin M.rank, k ≠ h →
    M.generators h i j < M.generators k i j

/-- The **extremal rank** of a transport semimodule. -/
def extremalRank (M : TransportSemimod I J) : ℕ := M.rank

/-! ## §4. Realization Functor -/

/-- Construct attention from a transport semimodule. -/
def transportToAttention (M : TransportSemimod I J) : MultiHeadAttn I J M.rank :=
  ⟨M.generators⟩

/-- Construct a transport semimodule from a separated architecture. -/
def attentionToTransport {n : ℕ} (A : MultiHeadAttn I J n)
    (hsep : IsSeparated A) : TransportSemimod I J where
  rank := n
  generators := A.heads
  combined := A.combined
  combined_spec := fun i j => by simp [MultiHeadAttn.combined]
  generators_essential := hsep

/-! ## §5. Core Lemmas -/

/-
Essential heads are not dominated.
-/


/-
Quantitative separation implies qualitative separation.
-/

/-- Sub-family combined kernel using `Finset.inf'`. -/
def SubFamilyCombined {n : ℕ} [DecidableEq (Fin n)] (A : MultiHeadAttn I J n)
    (S : Finset (Fin n)) (hS : S.Nonempty) (i : I) (j : J) : ℝ :=
  S.inf' hS (fun h => A.heads h i j)

/-
The full combined kernel equals the sub-family combined over `univ`.
-/

/-
**Essential head must be in any sub-family that realizes the combined kernel.**
-/

/-
**Irredundant head count is minimal**: any sub-family with the same combined
    kernel must include all heads of a separated architecture.
-/

/-! ## §6. Round-trip Theorems -/






/-! ## §7. Stability Under Perturbation -/

/-
**Perturbation preserves separation**: if `A` is separated with margin `δ`
    and `B` is within distance `δ/2` entrywise, then `B` is also separated.
-/


/-! ## §8. Certified Reconstruction -/

/-- Reconstruct attention from transport semimodule. -/
def reconstructFromTransport (M : TransportSemimod I J) : MultiHeadAttn I J M.rank :=
  transportToAttention M



/-! ## §9. Compression Corollaries -/







end TropicalAttention


