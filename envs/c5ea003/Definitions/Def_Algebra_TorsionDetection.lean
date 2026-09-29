-- Prove2me | Definitions.Def_Algebra_TorsionDetection
-- name    : Algebra_TorsionDetection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:15:34.725309+00:00
-- url     : https://prove2.me/theorems/4009fbd0-a8a9-4135-ab4d-0b0920a395d6
-- title:
--   Aether Catalog definitions — Algebra_TorsionDetection
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TorsionDetection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TorsionDetection.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Persistent Torsion Detection via Tor₁

This file formalizes a torsion-aware persistent homology theory over ℤ.

**Central insight**: Classical persistence over fields collapses torsion information.
The derived functor `Tor₁(ℤ/pℤ, -)` recovers it as a new persistent observable,
providing an arithmetic signature of topological features invisible to field-based methods.

## Main definitions

* `HasNoNTorsion` — Predicate that a module has no n-torsion
* `pTorsionDetected` — Predicate that Tor₁(ℤ/nℤ, A) is nontrivial (torsion exists)
* `torsionSupport` — The set of filtration indices where p-torsion is detected
* `torsionBirth` / `torsionDeath` — Birth and death of torsion in a filtration
* `PersistenceModule` — A functor from a preorder to ℤ-modules with structure maps
* `TorsionPersistence` — The torsion persistence module induced by Tor₁

## Main results (Catalog + New)

* `tor1_vanishes_iff_no_n_torsion` — Tor₁(ℤ/nℤ, A) vanishes iff A has no n-torsion
* `tor1_Zmod_free_vanishes_via_torsion` — Free ℤ-modules have vanishing Tor₁
* `tor1_persistent_detects_ptorsion` — Pointwise torsion detection in persistent homology
* `torsion_persistence_functorial` — Induced maps on torsion compose correctly
* `pTorPersistence_vanishes_of_free` — Free persistent homology ⟹ empty torsion barcode
* `exists_torsion_birth` — Existence of a torsion birth index in finite filtrations
* `prime_selectivity` — Different primes detect different torsion
* `torsion_invisible_wrong_characteristic` — Field-invisible torsion is Tor₁-visible
* `zmod_has_p_torsion` / `zmod_no_coprime_torsion` — Concrete computational verification
-/

/-! ## Section 1: Core Torsion Definitions

We define torsion predicates using the canonical `zsmul` from `AddCommGroup`,
avoiding the well-known SMul diamond between `SubNegMonoid.toZSMul` and
`DistribMulAction.toDistribSMul.toSMul` for ℤ-modules.

Mathematically, `Tor₁^ℤ(ℤ/nℤ, A) ≅ {a ∈ A : n·a = 0}` (the n-torsion subgroup),
computed via the 2-term free resolution `ℤ →(·n)→ ℤ → ℤ/nℤ → 0`.
We formalize the detection criterion: Tor₁ vanishes iff no torsion exists. -/

/-- A ℤ-module (abelian group) A has **no n-torsion** if the only element
    killed by multiplication by n is zero. Equivalently, `Tor₁^ℤ(ℤ/nℤ, A) = 0`. -/
def HasNoNTorsion (n : ℤ) (A : Type*) [AddCommGroup A] : Prop :=
  ∀ a : A, n • a = 0 → a = 0

/-- **p-torsion is detected** in A when there exists a nonzero element killed by p.
    Equivalently, `Tor₁^ℤ(ℤ/pℤ, A) ≠ 0` — the torsion detector "fires". -/
def pTorsionDetected (p : ℤ) (A : Type*) [AddCommGroup A] : Prop :=
  ∃ a : A, a ≠ 0 ∧ p • a = 0

/-! ## Section 2: Catalog Theorems — The Detection Engine -/



/-! ## Section 3: Persistent Torsion Detection — New Definitions -/

/-- The **torsion support** of a family of abelian groups: the set of indices
    where p-torsion is detected. This is the support of the "torsion barcode" —
    the interval decomposition of torsion phenomena along a filtration. -/
def torsionSupport {ι : Type*}
    (p : ℤ) (H : ι → Type*) [∀ i, AddCommGroup (H i)] : Set ι :=
  {i | pTorsionDetected p (H i)}



/-! ## Section 4: Persistence Module Structure -/

/-- A **persistence module** over ℤ indexed by a preorder ι.
    This packages a family of abelian groups with ℤ-linear structure maps
    satisfying identity and composition laws — the categorical backbone
    of persistent homology. -/
structure PersistenceModule (ι : Type*) [Preorder ι] where
  /-- The abelian group at each filtration index -/
  obj : ι → Type*
  /-- Each group is an abelian group -/
  [instAG : ∀ i, AddCommGroup (obj i)]
  /-- Each group has a ℤ-module structure -/
  [instMod : ∀ i, Module ℤ (obj i)]
  /-- Structure map from index i to index j when i ≤ j -/
  map : ∀ {i j : ι}, i ≤ j → obj i →ₗ[ℤ] obj j
  /-- The identity map -/
  map_id : ∀ (i : ι) (x : obj i), map (le_refl i) x = x
  /-- Composition law -/
  map_comp : ∀ {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : obj i),
    map hjk (map hij x) = map (le_trans hij hjk) x

attribute [instance] PersistenceModule.instAG PersistenceModule.instMod

/-! ## Section 5: Functoriality of Tor₁ — The Key Innovation

A ℤ-linear map f : A → B induces a map on torsion: if n • a = 0, then
n • f(a) = f(n • a) = f(0) = 0. This makes Tor₁(ℤ/nℤ, -) a functor.
When applied to a persistence module, it produces a new persistence module —
the **torsion persistence module**, a derived invariant for TDA.

We formalize this by showing that maps on torsion respect identity and composition,
establishing Tor₁ as a genuine endofunctor on persistence modules. -/





/-! ## Section 6: Theorem 1 — Pointwise Tor-detects-p-torsion in Persistent Homology -/



/-! ## Section 7: Theorem 3 — Free Persistent Homology Implies Vanishing Torsion -/



/-! ## Section 8: Theorem 4 — Existence of Torsion Birth in Finite Filtrations

For a linearly ordered filtration, if torsion is absent at some index and
present at a later index, there must be a first index where torsion appears.
This gives the formal backbone of a torsion barcode. -/

/-
**Torsion Birth Theorem**: For a well-founded linearly ordered filtration,
    if torsion is absent at index i₀ and present at index i₁ ≥ i₀,
    then there exists a first birth index b ∈ [i₀, i₁].

    The well-foundedness condition is necessary (without it, there might be
    no first torsion index, e.g., H(q) has torsion for all q > 0 in ℚ).
    Finite filtrations and ℕ-indexed filtrations satisfy this automatically.
-/

/-! ## Section 9: Prime Selectivity — The Arithmetic Signature -/



/-! ## Section 10: Concrete Examples — Computational Verification -/


