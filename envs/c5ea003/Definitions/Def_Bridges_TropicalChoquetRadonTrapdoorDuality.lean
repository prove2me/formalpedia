-- Prove2me | Definitions.Def_Bridges_TropicalChoquetRadonTrapdoorDuality
-- name    : Bridges_TropicalChoquetRadonTrapdoorDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:55.248614+00:00
-- url     : https://prove2.me/theorems/b69fe572-5c14-473b-8538-b1733d9ab8e4
-- title:
--   Aether Catalog definitions — Bridges_TropicalChoquetRadonTrapdoorDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalChoquetRadonTrapdoorDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalChoquetRadonTrapdoorDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Choquet–Radon Trapdoor Duality via Idempotent Convex Semimodules
# and Certified Extremal Decomposition

## Overview

This file formalizes a duality between **geometric exposedness** and **algorithmic
invertibility** in tropical convex systems, establishing the mathematical foundation
for *tropical convex cryptography*.

The core phenomenon: in a tropical Choquet system with intersection-stable supports,
every element has a unique canonical minimal support (`suppC`). Under a separation
axiom (prime congruence separation), the public Radon profile uniquely determines this
hidden support — enabling a **trapdoor inversion** on the "exposed" subclass. Conversely,
failure of exposedness forces **collision families**: distinct supports with identical
profiles, creating cryptographic ambiguity.

## Main Results

### Theorem 1: Canonical Minimal Extremal Support
`exists_unique_minimal_extremal_support` — Every element has a unique minimal support,
the intersection of all decomposition supports. This creates the **private key object**.

### Theorem 2: Radon Inversion on the Separated/Exposed Class
`radonProfile_injective_on_support` — Under prime congruence separation, the Radon
profile uniquely determines the canonical support on the exposed subclass. This is the
**public-key half**: inversion is possible in principle and canonical.

### Theorem 3: Trapdoor Rigidity / Certified Recovery
`recoverSupport_correct` — A computable recovery algorithm reconstructs the canonical
support from the Radon profile in O(|E|) steps on the exposed class. This is the
actual **trapdoor**.

### Theorem 4: Obstruction / Collision Families under Non-Exposedness
`exists_collision_of_not_exposed` — Failure of global exposedness produces collision
families: distinct supports with identical profiles. This is the **hardness side**.

## Cross-Domain Connections

- **Tropical convexity × Cryptography**: Canonical support = private key,
  Radon profile = public image. Exposedness ↔ invertibility.
- **Idempotent analysis × Integral geometry**: Choquet decomposition + Radon
  measurement = tropical tomography of sparse convex states.
- **Prime congruences × Hardness**: Semiring congruences are the algebraic source
  of support collapse and cryptographic ambiguity.
- **Sparse recovery × Tropical inversion**: The recovery theorem is a tropical
  analogue of exact sparse support recovery from measurement data.

## Relationship to Prior Work

Builds conceptually on `certified_finite_tropical_decomposition` from
`TropicalChoquetClosureDuality`, which establishes that tropical max functionals
admit canonical finite decompositions with unique weights and irredundant support.
This file lifts that decomposition theory to a cryptographic duality framework.

Connects to the obstruction technology behind `tropical_hash_collision_obstruction`:
non-exposedness induces the same congruence-collapse mechanism that forces
hash collisions in tropical hashing.

## Keywords

tropical convex cryptography, idempotent convex semimodules, tropical Choquet theory,
tropical Radon inversion, canonical extremal support, exposed extremals,
prime congruence separation, valuation collapse, collision families,
trapdoor inversion, sparse support recovery, tropical tomography,
idempotent functional analysis, semiring cryptography, geometric one-way structures
-/

open Classical Finset

noncomputable section

namespace TropicalChoquetRadon

/-! ## Core Structures -/

/-- A **tropical Choquet system** encodes a finite tropical convex decomposition
    framework over a type `M` of elements, with extremal generators indexed by a
    finite type `E` and coefficients in a semiring `S`.

    The key axiom `supports_inter` (intersection-stability of supports) is the
    tropical analogue of the anti-exchange property in convex geometry. It ensures
    that the canonical minimal support is well-defined. -/
structure TropicalChoquetSystem (S E M : Type*) [Fintype E] [DecidableEq E] where
  /-- Evaluation: maps coefficient profiles over extremal generators to elements -/
  eval : (E → S) → M
  /-- Support predicate: `Supports x K` means `x` admits a certified tropical
      decomposition using only generators in `K` -/
  Supports : M → Finset E → Prop
  /-- Every element has at least one support (existence of decomposition) -/
  has_support : ∀ x : M, ∃ K : Finset E, Supports x K
  /-- Supports are upward-closed: adding unused generators preserves support -/
  supports_mono : ∀ {x : M} {K L : Finset E}, Supports x K → K ⊆ L → Supports x L
  /-- **Intersection stability**: if both `K` and `L` support `x`, then `K ∩ L`
      supports `x`. This is the decisive axiom enabling canonical decomposition. -/
  supports_inter : ∀ {x : M} {K L : Finset E},
    Supports x K → Supports x L → Supports x (K ∩ L)

/-- A **tropical Radon system** provides a public profile map from elements to a
    finite observation type, together with a predicate identifying the
    "exposed-separated" subclass on which profile-based detection is reliable.

    In the cryptographic interpretation:
    - `profile` is the public key / hash function
    - `ExposedSeparated` identifies the "nice" subclass where inversion works -/
structure TropicalRadonSystem (E M P : Type*) where
  /-- The public profile map: sends elements to their observable Radon data -/
  profile : M → P
  /-- The exposed-separated predicate: identifies the rigid subclass -/
  ExposedSeparated : M → Prop

variable {S E M P : Type*} [Fintype E] [DecidableEq E]

/-! ## Section 1: Support Infrastructure -/

/-- The finset of all supports of `x`, as a `Finset (Finset E)`.
    Since `E` is a `Fintype`, `Finset E` is also a `Fintype`, so we can
    enumerate all subsets and filter for supports. -/
def TropicalChoquetSystem.supportFinset (TC : TropicalChoquetSystem S E M)
    (x : M) : Finset (Finset E) :=
  Finset.univ.filter (TC.Supports x)

/-- The support finset is nonempty: every element has at least one support. -/
theorem TropicalChoquetSystem.supportFinset_nonempty
    (TC : TropicalChoquetSystem S E M) (x : M) :
    (TC.supportFinset x).Nonempty := by
  obtain ⟨K, hK⟩ := TC.has_support x
  exact ⟨K, mem_filter.mpr ⟨mem_univ K, hK⟩⟩


/-! ## Section 2: Canonical Minimal Support (`suppC`) -/

/-- The **canonical minimal support** of `x`: the infimum (intersection) of all
    supports in the support lattice `(Finset E, ⊆)`.

    This is the tropical analogue of the Choquet boundary — the smallest set of
    extremal generators needed to represent `x`.

    The definition uses `Finset.inf'` on the nonempty collection of all supports,
    with the lattice infimum on `Finset E` being set intersection. -/
def TropicalChoquetSystem.suppC (TC : TropicalChoquetSystem S E M)
    (x : M) : Finset E :=
  (TC.supportFinset x).inf' (TC.supportFinset_nonempty x) id


/-
A predicate on `Finset E` that is closed under `⊓` (intersection) is
    preserved by `Finset.inf'`. This is used to show that the intersection
    of all supports is itself a support.
-/

/-
The canonical support is itself a valid support of `x`.
    This is the key consequence of intersection-stability (`supports_inter`):
    the intersection of all supports, being the infimum in the support lattice,
    is itself a support.
-/

/-
**Theorem 1: Canonical Minimal Extremal Support.**
    Every element has a unique minimal support, characterized as the intersection
    of all decomposition supports.

    *Mathematical content*: Let `S` be a coefficient semiring, `E` a finite type of
    extremal generators, and `M` a tropical convex `S`-semimodule with
    intersection-stable supports. Then for every `x : M`, there exists a unique
    `suppC x : Finset E` such that:
    1. `suppC x` supports a certified decomposition of `x`
    2. For any support `T` of `x`, `suppC x ⊆ T`
    3. Hence `suppC x` is the unique minimal support

    This theorem creates the **private key object**: the canonical extremal support.
    Without a canonical support notion, "trapdoor inversion" is just rhetoric.
    With it, tropical convex decomposition becomes a cryptographic state space.

    *Cross-domain*: This is the tropical analogue of the Choquet–Bishop–de Leeuw
    theorem for finite extremal decompositions.
-/

/-
The canonical support equals the finset intersection of all supports.
    This is the explicit characterization of `suppC` as a universal intersection.
-/


/-! ## Section 3: Radon Separation and Profile Injectivity -/

/-- **Prime congruence separation**: each extremal generator is detectable by a
    profile test on the exposed subclass.

    For every generator `e : E`, there exists a predicate `test` on profiles
    such that for all exposed-separated elements `x`, the test detects whether
    `e` belongs to the canonical support of `x`.

    This is the tropical analogue of point separation by continuous linear
    functionals in classical convex geometry. It says that the Radon measurement
    system has enough "resolution" to individually detect each extremal generator. -/
def HasPrimeCongruenceSeparation (TC : TropicalChoquetSystem S E M)
    (RP : TropicalRadonSystem E M P) : Prop :=
  ∀ e : E, ∃ test : P → Prop,
    ∀ x : M, RP.ExposedSeparated x → (test (RP.profile x) ↔ e ∈ TC.suppC x)

/-
**Theorem 2: Radon Profile Injectivity on the Exposed Class.**
    Under prime congruence separation, two exposed-separated elements with the
    same Radon profile have the same canonical support.

    *Proof sketch*: For each generator `e : E`, the separation axiom provides a
    test `test_e` such that `test_e (profile x) ↔ e ∈ suppC x` for exposed `x`.
    If `profile x = profile y`, then `test_e (profile x) = test_e (profile y)`,
    so `e ∈ suppC x ↔ e ∈ suppC y`. Since this holds for all `e`, the supports
    are equal by extensionality.

    *Cross-domain*: This is the public-key half of the tropical cryptographic
    duality. On the rigid class, the public Radon profile determines the hidden
    extremal support — a tropical analogue of "structured one-wayness with a
    trapdoor subclass."
-/

/-
Contrapositive form: distinct canonical supports imply distinct profiles
    on the exposed class.
-/

/-! ## Section 4: Certified Recovery Algorithm -/

/-- A **certified exposed basis** provides computable boolean tests for each
    generator that correctly detect support membership from profiles on the
    exposed subclass.

    In the cryptographic interpretation, these tests are the "trapdoor
    information" — knowledge of the test battery enables efficient inversion. -/
def HasCertifiedExposedBasis (TC : TropicalChoquetSystem S E M)
    (RP : TropicalRadonSystem E M P) (tests : E → P → Bool) : Prop :=
  ∀ e : E, ∀ x : M, RP.ExposedSeparated x →
    (tests e (RP.profile x) = true ↔ e ∈ TC.suppC x)

/-- The **support recovery algorithm**: given a battery of boolean tests
    (one per generator) and a profile value, recover the support by filtering
    generators through the tests.

    Complexity: exactly `|E|` test evaluations (one per generator). -/
def recoverSupport (tests : E → P → Bool) (p : P) : Finset E :=
  Finset.univ.filter (fun e => tests e p)

/-
**Theorem 3: Certified Recovery Correctness.**
    On exposed-separated elements, the recovery algorithm exactly reconstructs
    the canonical support from the Radon profile.

    This is the actual **trapdoor**: knowledge of the certified test battery
    (the "private key structure") enables efficient inversion of the
    profile-to-support map. Combined with Theorem 2, this gives:
    - The profile uniquely determines the support (Theorem 2)
    - The support can be efficiently computed from the profile (Theorem 3)
    - Both require the "trapdoor" (test battery / separation data)
-/

/-
The recovered support has at most `|E|` elements (trivial step bound).
-/

/-
A certified exposed basis implies prime congruence separation.
    The boolean tests provide decidable separation predicates.
-/

/-! ## Section 5: Collision Obstruction -/

/-- **Global exposedness**: the profile map is injective on canonical supports
    across *all* elements (not just the exposed subclass).

    This is the strongest possible separation property. When it fails,
    collision families necessarily exist. -/
def GlobalExposedness (TC : TropicalChoquetSystem S E M)
    (RP : TropicalRadonSystem E M P) : Prop :=
  ∀ x y : M, RP.profile x = RP.profile y → TC.suppC x = TC.suppC y

/-- **Valuation congruence**: two elements are valuation-congruent if they have
    identical profiles. This is the tropical analogue of prime-congruence
    indistinguishability — elements that are algebraically indistinguishable
    under all Radon tests. -/
def ValuationCongruent (RP : TropicalRadonSystem E M P) (x y : M) : Prop :=
  RP.profile x = RP.profile y




/-
**Theorem 4: Collision Families under Non-Exposedness.**
    Failure of global exposedness produces collision families: pairs of elements
    with distinct canonical supports but identical Radon profiles.

    This is the hardness side of the duality. Without exposedness, the
    profile-to-support map is necessarily ambiguous, creating cryptographic
    collision families. The collision mechanism mirrors the congruence collapse
    in `tropical_hash_collision_obstruction`: non-exposedness induces
    indistinguishable support pairs via prime congruence collapse.

    *Cross-domain*: This is the formal obstruction that makes the trapdoor
    non-trivial. In classical terms: without the separation data (the "private
    key"), the public profile does not determine the hidden support.
-/

/-
Sharper collision theorem with explicit valuation congruence witness:
    the colliding pairs are prime-congruence indistinguishable.
-/

/-! ## Section 6: The Trapdoor Duality Dichotomy -/

/-
**The trapdoor duality dichotomy**: either the system has global exposedness
    (enabling canonical recovery for all elements) or it has collision families
    (creating cryptographic ambiguity). There is no middle ground.

    This is the central duality theorem:
    - **Rigid exposed class** ⇒ canonical inversion (Theorems 2–3)
    - **Non-exposed class** ⇒ forced ambiguity/collisions (Theorem 4)

    The dichotomy is clean and complete: every tropical Choquet–Radon system
    falls into exactly one of these two cases.
-/

/-! ## Section 7: Support Monotonicity and Structural Lemmas -/

/-
The canonical support is monotone under system refinement:
    if system TC₂ has more supports than TC₁ (more decompositions available),
    then the canonical support in TC₂ is smaller (more constraints satisfied).
-/

/-
The symmetric difference of two distinct finsets is nonempty.
-/

/-
Distinguished extremal witness: if supports differ, there exists a generator
    in one but not the other.
-/

/-! ## Section 8: Concrete Instantiation

We provide a concrete example showing the structures are satisfiable:
a tropical Choquet system on `Fin n → ℕ` with max-plus evaluation. -/

/-- A concrete tropical Choquet system on `Fin n → ℕ` where support means
    the set of coordinates with nonzero coefficient.
    This demonstrates the structures are non-vacuously satisfiable. -/
def concreteTropicalSystem (n : ℕ) [NeZero n] :
    TropicalChoquetSystem ℕ (Fin n) (Fin n → ℕ) where
  eval := id
  Supports := fun x K => ∀ e : Fin n, x e ≠ 0 → e ∈ K
  has_support := fun x => ⟨Finset.univ, fun _ _ => Finset.mem_univ _⟩
  supports_mono := fun hK hKL e he => hKL (hK e he)
  supports_inter := fun hK hL e he => Finset.mem_inter.mpr ⟨hK e he, hL e he⟩

/-
The canonical support in the concrete system equals the set of nonzero
    coordinates.
-/

end TropicalChoquetRadon


