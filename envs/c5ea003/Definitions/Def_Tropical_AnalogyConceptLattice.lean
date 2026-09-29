-- Prove2me | Definitions.Def_Tropical_AnalogyConceptLattice
-- name    : Tropical_AnalogyConceptLattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:12.737667+00:00
-- url     : https://prove2.me/theorems/dfaf98ea-bfab-41ce-b63b-69c2b5f51339
-- title:
--   Aether Catalog definitions — Tropical_AnalogyConceptLattice
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AnalogyConceptLattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AnalogyConceptLattice.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# Analogy on the Concept Lattice — the Adjoint (Galois) Model

Hofstadter's *Copycat* operates on a lattice of concepts.  In formal concept
analysis, the canonical structure-preserving analogy between two concept
lattices is a **Galois connection** `l ⊣ u`.  This file develops the adjoint
model of analogy: an analogy is *optimal* precisely when the round-trips
`u ∘ l` and `l ∘ u` are stable (closure / kernel operators), and the backward
map is then uniquely determined by the forward map.

## Main results

* `adjointAnalogy_extensive`      — `a ≤ u (l a)`: the concept is refined by the round trip.
* `adjointAnalogy_stable_closure` — `u ∘ l` is idempotent (a closure operator).
* `adjointAnalogy_stable_kernel`  — `l ∘ u` is idempotent (a kernel operator).
* `adjointAnalogy_monotone`       — the round trip `u ∘ l` is monotone.
* `adjoint_unique`                — **the inverse of an adjoint analogy is unique**:
  a given forward map has at most one adjoint backward map.
* `copycat_isAdjoint`             — the identity ("copycat") analogy on a single
  concept lattice is an adjoint analogy.
* `copycat_roundtrip_id`          — the copycat round trip is the identity (zero distortion).
-/

namespace TropicalAnalogy

variable {L M : Type*}

/-- An **adjoint analogy** between concept (pre)orders `L` and `M` is a Galois
connection: monotone maps `l : L → M`, `u : M → L` with `l a ≤ b ↔ a ≤ u b`. -/
abbrev AdjointAnalogy [Preorder L] [Preorder M] (l : L → M) (u : M → L) : Prop :=
  GaloisConnection l u

/-
Every concept is refined by the analogical round trip: `a ≤ u (l a)`.
-/

/-
The round trip `u ∘ l` of an adjoint analogy is **idempotent**: applying the
analogy twice gives the same refined concept as applying it once.  This is the
formal statement that `u ∘ l` is a closure operator.
-/

/-
Dually, `l ∘ u` is idempotent (a kernel/interior operator).
-/

/-
The analogical round trip `u ∘ l` is monotone.
-/

/-
**Uniqueness of the adjoint (the "best" backward analogy is unique).**
If a forward analogy `l` admits two adjoint backward maps `u₁` and `u₂`, they
must coincide.  So the optimal inverse of an analogy, when it exists, is
determined by the forward map.
-/

/-
**The copycat analogy is an adjoint analogy.**  On a single concept lattice
`L`, the identity-on-both-sides analogy is a Galois connection.
-/

/-
**The copycat analogy is rigid.**  On a concept lattice `L`, the copycat's
forward map (the identity) admits a *unique* adjoint backward map, namely the
identity itself.  Combined with `copycat_isAdjoint` this says the identity is
its own unique adjoint: the copycat is a perfect, self-dual analogy of a
lattice with itself (zero distortion, `u ∘ l = id`).
-/

end TropicalAnalogy


