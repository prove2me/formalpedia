-- Prove2me | Definitions.Def_Bridges_TropicalObserverCodingDuality
-- name    : Bridges_TropicalObserverCodingDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:45.49233+00:00
-- url     : https://prove2.me/theorems/83d740a9-b4ca-4456-a2b5-11301a0132cb
-- title:
--   Aether Catalog definitions — Bridges_TropicalObserverCodingDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalObserverCodingDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalObserverCodingDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Observer Coding Duality

A finite representation/minimality theorem: tropical separation objects built from
proof observers are equivalent to canonical minimal proof-compression architectures.
Observer codes and compression networks are mathematically equivalent finite objects,
with a recoverable distance geometry and a certified minimality invariant.

## Main Results

### Definitions
* `CodeEqFamily` — code equivalence under a family of observer functionals
* `SubfamilySeparates` — a subfamily separates inequivalent states
* `observerDist` — tropical separation pseudodistance (sup of coordinate distances)
* `subDist` — subfamily-restricted distance
* `TropicalSeparationSemimodule` — bundled certified separation data
* `MinimalCompressionNetwork` — minimal layered proof-compression architecture
* `ObserverSeparationRank` — minimal width of a separating observer subfamily
* `CompressionNetworkIso` — isomorphism between minimal networks
* `CanonicalDistProfile` — distance profile function
* `RealizesSemimodule` — realization relation between networks and semimodules

### Theorems (flagship results)
* `observerDist_refl` — reflexivity of tropical distance
* `observerDist_symm` — symmetry of tropical distance
* `observerDist_triangle` — triangle inequality for tropical distance
* `observerDist_eq_zero_iff` — separation characterization
* `compression_nonexpansive_of_coord` — coordinate nonexpansivity implies global
* `tropical_distance_descends_codeEq` — distance respects code equivalence
* `exists_minimal_separating_subfamily` — existence of minimal separating subfamily
* `spectral_witness_implies_irredundant` — spectral witnesses certify irredundancy
* `minimal_subfamily_card_unique` — uniqueness of separation rank
* `reconstruct_network_from_subfamily` — reconstruction from minimal subfamily
* `finite_separation_semimodule_realization_minimal` — flagship duality theorem

## Bridge

Connects tropical algebra (max-plus coordinates) ↔ proof compression (state contraction)
↔ coding theory (separating codes) ↔ automata minimization (Myhill–Nerode) ↔
metric learning (certified representation geometry) ↔ neural architecture (minimal width).

Builds on `canonical_observer_code_certified` from `ObserverRateDistortion.lean`.

## Cross-domain significance

- **Automata theory**: observer separation rank as tropical Nerode index
- **Metric learning**: canonical distance profile as certified representation metric
- **Neural compression**: minimal observer width as intrinsic latent dimension
- **Proof theory**: proof-state contraction as semantics-preserving compression
- **Tropical geometry**: max-plus coordinates as architecture geometry
- **Coding theory**: finite observer codes as separating codes on proof states
-/

set_option maxHeartbeats 800000

open Finset Function

noncomputable section

namespace TropicalObserverDuality

/-! ## §1. Observer Families and Code Equivalence -/

/-- Code equivalence under a family of observer functionals: two states are
    code-equivalent if all observers assign them the same value.
    This is the kernel of the combined observation map `x ↦ (Φ i x)_i`. -/
def CodeEqFamily {S ι : Type*} (Φ : ι → S → ℤ) (x y : S) : Prop :=
  ∀ i : ι, Φ i x = Φ i y




/-- A family of observer functionals **separates** if code-equivalence implies equality.
    This is injectivity of the combined observation map. -/
def SeparatesCodeEqFamily {S ι : Type*} (Φ : ι → S → ℤ) : Prop :=
  ∀ x y : S, CodeEqFamily Φ x y → x = y

/-- A **subfamily** separates if the restricted family of observers still
    distinguishes all inequivalent states. -/
def SubfamilySeparates {S ι : Type*} (Φ : ι → S → ℤ) (J : Finset ι) : Prop :=
  ∀ x y : S, (∀ i ∈ J, Φ i x = Φ i y) → x = y


/-
Subfamily separation is anti-monotone: larger subfamilies separate at least as well
    (more observers = stronger separation).
-/

/-- An observer index `i` is a **spectral witness** for the family `Φ` if
    there exist states that are separated by observer `i` but not by any other
    single observer in the complement. This certifies that `i` is essential. -/
def SpectralWitnessFor {S ι : Type*} [DecidableEq ι]
    (Φ : ι → S → ℤ) (J : Finset ι) (i : ι) : Prop :=
  i ∈ J ∧ ∃ x y : S, (∀ j ∈ J.erase i, Φ j x = Φ j y) ∧ Φ i x ≠ Φ i y

/-- An observer index is **irredundant** in a separating subfamily if removing
    it breaks separation. -/
def GeneratorIrredundant {S ι : Type*} [DecidableEq ι]
    (Φ : ι → S → ℤ) (J : Finset ι) (i : ι) : Prop :=
  i ∈ J ∧ ¬SubfamilySeparates Φ (J.erase i)

/-! ## §2. Tropical Coordinate Distance -/

/-- The tropical separation pseudodistance between two states under observer
    family `Φ`, defined as the supremum of coordinate-wise absolute differences.
    This is the ℓ∞-norm in observer coordinate space.

    When `ι` is empty, the distance is 0 (vacuous observation). -/
def observerDist {S ι : Type*} [Fintype ι] (Φ : ι → S → ℤ) (x y : S) : ℕ :=
  Finset.sup Finset.univ (fun i => (Φ i x - Φ i y).natAbs)

/-- Subfamily-restricted distance: sup of coordinate distances over a subset. -/
def subDist {S ι : Type*} (Φ : ι → S → ℤ) (J : Finset ι) (x y : S) : ℕ :=
  J.sup (fun i => (Φ i x - Φ i y).natAbs)

/-! ## §3. Pseudometric Properties of Tropical Distance -/

/-
**Reflexivity**: the tropical distance from any state to itself is zero.
-/

/-
**Symmetry**: tropical distance is symmetric.
-/

/-
Coordinate-wise triangle inequality for `natAbs`.
-/

/-
Finset.sup of sum is bounded by sum of Finset.sup.
-/

/-
**Triangle inequality**: the tropical distance satisfies the triangle inequality.
-/

/-! ## §4. Separation Characterization -/

/-
Each coordinate distance is bounded by the overall tropical distance.
-/

/-
**Separation characterization**: the tropical distance is zero if and only if
    the two states are code-equivalent under all observers.

    This is the fundamental bridge between metric geometry and algebraic coding:
    vanishing distance ↔ observational indistinguishability.
-/

/-
Positive distance implies existence of a distinguishing observer.
-/

/-
For separating families, positive distance characterizes inequality.
-/

/-! ## §5. Compression Nonexpansivity -/

/-
**Compression nonexpansivity**: if each observer coordinate is nonexpansive
    under compression `C`, then the overall tropical distance is nonexpansive.

    Bridge: this connects proof-state compression to certified robustness —
    coordinate-wise contraction implies global metric contraction.
-/

/-
Compression preserves code equivalence.
-/

/-! ## §6. Distance Descends to Code Equivalence Classes -/

/-
**Tropical distance descends to CodeEq**: if an observer family respects
    code equivalence (i.e., observer values are constant on CodeEq classes),
    then the tropical distance is well-defined on the quotient.

    This gives the quotient geometry: the distance profile is a certified
    invariant of proof-state equivalence classes.
-/

/-! ## §7. Spectral Irredundancy -/

/-
**Spectral witness implies irredundancy**: if observer `i` has a spectral
    witness (a pair of states separated only by `i` among the subfamily),
    then removing `i` breaks separation.

    Bridge: this is where the speculative spectral infrastructure becomes
    mathematically decisive — spectral witnesses certify that generators
    cannot be removed from the architecture.
-/

/-! ## §8. Minimal Separating Subfamily -/


/-
**Existence of minimal separating subfamily**: for any finite separating
    observer family over a finite state space, there exists a subfamily of
    minimum cardinality that still separates.

    This is the finite combinatorial heart of the duality: the separation rank
    is well-defined because the state set is finite.

    Bridge: this is the tropical analogue of Myhill–Nerode minimization —
    observer separation rank behaves like a tropical state complexity invariant.
-/
theorem exists_minimal_separating_subfamily
    {S ι : Type*} [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (Φ : ι → S → ℤ) (hsep : SeparatesCodeEqFamily Φ) :
    ∃ J : Finset ι,
      SubfamilySeparates Φ J ∧
      ∀ K : Finset ι, SubfamilySeparates Φ K → J.card ≤ K.card := by
  have h_nonempty : ∃ J : Finset ι, SubfamilySeparates Φ J := by
    exact ⟨ Finset.univ, fun x y hxy => hsep x y fun i => hxy i ( Finset.mem_univ i ) ⟩;
  apply_rules [ Set.exists_min_image ];
  exact Set.toFinite _

/-- The separation rank: minimal cardinality of a separating subfamily. -/
def ObserverSeparationRank {S ι : Type*} [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (Φ : ι → S → ℤ) (hsep : SeparatesCodeEqFamily Φ) : ℕ :=
  (exists_minimal_separating_subfamily Φ hsep).choose.card



/-
**Uniqueness of separation rank**: any two minimal separating subfamilies
    have the same cardinality.
-/

/-! ## §9. Structures: Semimodule, Network, Realization -/

/-- A **tropical separation semimodule** bundles a finite observer family with
    certified separation, compression nonexpansivity, and generator irredundancy.

    This is the algebraic side of the duality: a finitely generated idempotent
    separation structure over observer functionals on a finite state space. -/
structure TropicalSeparationSemimodule (S : Type*) [Fintype S] [DecidableEq S] where
  /-- Number of generators (observer coordinates) -/
  numGen : ℕ
  /-- Observer functionals: tropical-valued score maps on states -/
  observers : Fin numGen → S → ℤ
  /-- Compression action on states -/
  compression : S → S
  /-- The observer family separates inequivalent states -/
  separates : SeparatesCodeEqFamily observers
  /-- Each coordinate is nonexpansive under compression -/
  coordNonexpansive : ∀ i x y,
    (observers i (compression x) - observers i (compression y)).natAbs ≤
    (observers i x - observers i y).natAbs


/-- The observer separation rank of a semimodule. -/
def TropicalSeparationSemimodule.sepRank
    {S : Type*} [Fintype S] [DecidableEq S]
    (M : TropicalSeparationSemimodule S) : ℕ :=
  ObserverSeparationRank M.observers M.separates

/-- The canonical distance profile of a semimodule. -/
def TropicalSeparationSemimodule.CanonicalDistProfile
    {S : Type*} [Fintype S] [DecidableEq S]
    (M : TropicalSeparationSemimodule S) : S → S → ℕ :=
  observerDist M.observers



/-- A **minimal compression network** is a finite layered architecture whose
    hidden coordinates are exactly the essential generators.

    Bridge: this is the algorithmic/architectural side of the duality —
    the network whose width equals the separation rank. -/
structure MinimalCompressionNetwork (S : Type*) [Fintype S] [DecidableEq S] where
  /-- Width = number of observer coordinates -/
  ObserverWidth : ℕ
  /-- Network coordinates: the observer functionals -/
  coordinates : Fin ObserverWidth → S → ℤ
  /-- Compression map -/
  compression : S → S
  /-- The coordinates separate states -/
  separates : SeparatesCodeEqFamily coordinates
  /-- Coordinate-wise nonexpansivity -/
  coordNonexpansive : ∀ i x y,
    (coordinates i (compression x) - coordinates i (compression y)).natAbs ≤
    (coordinates i x - coordinates i y).natAbs
  /-- Minimality: no proper subfamily separates -/
  minimal : ∀ J : Finset (Fin ObserverWidth),
    SubfamilySeparates coordinates J → J.card = ObserverWidth


/-- A network **realizes** a separation semimodule if they induce the same
    distance profile and code equivalence classes. -/
def RealizesSemimodule {S : Type*} [Fintype S] [DecidableEq S]
    (N : MinimalCompressionNetwork S) (M : TropicalSeparationSemimodule S) : Prop :=
  (∀ x y, CodeEqFamily N.coordinates x y ↔ CodeEqFamily M.observers x y) ∧
  N.compression = M.compression


/-! ## §10. Reconstruction from Minimal Subfamily -/

/-
**Reconstruction theorem**: from a minimal separating subfamily, construct
    a minimal compression network with matching width and structure.
-/

/-! ## §11. Flagship Duality Theorem -/

/-
Helper: if a subfamily separates and all its observers agree on x, y,
    then x = y, so CodeEqFamily holds by reflexivity.
-/


/-
**Flagship Theorem: Finite Separation Semimodule Realization Minimality.**

    For every finite proof-state type `S`, every tropical separation semimodule `M`
    admits a finite minimal layered proof-compression network `N` such that
    `N` realizes the same `CodeEq`-classes as `M` and has width equal to the
    separation rank (the minimum number of observers needed).
-/

/-! ## §12. Connecting to `canonical_observer_code_certified` -/


/-! ## §13. SubDist Properties and Embedding -/

/-
SubDist reflexivity.
-/

/-
SubDist symmetry.
-/

/-
SubDist is bounded by full observerDist.
-/

/-
SubDist zero iff all observers in J agree.
-/

/-
**Tropical embedding theorem for CodeEq quotient**: a separating family
    induces an injective map from states into ℤ^n. This makes the observer
    coordinate map a faithful finite tropical embedding.
-/

/-! ## §14. Compression Orbit and Convergence -/

/-
Iterated compression distances are nonincreasing: the orbit diameter
    shrinks monotonically under coordinate-nonexpansive compression.
-/

/-
Over a finite state space, compression orbits are eventually periodic:
    there exist indices m < n with the same iterate value.
-/

end TropicalObserverDuality


