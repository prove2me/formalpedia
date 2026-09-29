-- Prove2me | solution 1 for TropicalObserverDuality.reconstruct_network_from_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:30.091812+00:00
-- url     : https://prove2.me/submissions/6eba6f13-4db0-4397-9109-678724ceeffa

-- Sol generated from Bridges/TropicalObserverCodingDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalObserverCodingDuality
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

open TropicalObserverDuality

/-! ## §1. Observer Families and Code Equivalence -/








/-
Subfamily separation is anti-monotone: larger subfamilies separate at least as well
    (more observers = stronger separation).
-/



/-! ## §2. Tropical Coordinate Distance -/



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




/-
**Uniqueness of separation rank**: any two minimal separating subfamilies
    have the same cardinality.
-/

/-! ## §9. Structures: Semimodule, Network, Realization -/











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


open TropicalObserverDuality in
theorem solution    {S : Type*} [Fintype S] [DecidableEq S]
    {n : ℕ} (Φ : Fin n → S → ℤ) (C : S → S)
    (J : Finset (Fin n))
    (hJsep : SubfamilySeparates Φ J)
    (hJmin : ∀ K : Finset (Fin n), SubfamilySeparates Φ K → J.card ≤ K.card)
    (hcontr : ∀ i x y, (Φ i (C x) - Φ i (C y)).natAbs ≤ (Φ i x - Φ i y).natAbs) :
    ∃ N : MinimalCompressionNetwork S,
      N.ObserverWidth = J.card ∧
      N.compression = C ∧
      (∀ x y, CodeEqFamily N.coordinates x y ↔ ∀ i ∈ J, Φ i x = Φ i y) := by
  refine' ⟨ _, _, _, _ ⟩;
  exact ⟨ J.card, fun i x => Φ ( J.orderEmbOfFin rfl i ) x, C, by
    intro x y hxy
    have h_eq : ∀ i ∈ J, Φ i x = Φ i y := by
      intro i hi;
      obtain ⟨ j, hj ⟩ := Finset.mem_image.mp ( show i ∈ Finset.image ( fun j : Fin J.card => J.orderEmbOfFin rfl j ) Finset.univ from by aesop ) ; aesop;
    exact hJsep x y h_eq, by
    grind, by
    intro K hKsep
    have hKcard : K.card ≥ J.card := by
      refine' le_trans ( hJmin ( Finset.image ( fun i : Fin #J => J.orderEmbOfFin rfl i ) K ) _ ) _;
      · intro x y hxy;
        exact hKsep x y fun i hi => hxy _ ( Finset.mem_image_of_mem _ hi );
      · exact Finset.card_image_le;
    exact le_antisymm ( le_trans ( Finset.card_le_univ _ ) ( by simp +decide ) ) hKcard ⟩;
  · rfl;
  · rfl;
  · intro x y;
    constructor;
    · intro h i hi;
      obtain ⟨ j, hj ⟩ := Finset.mem_image.mp ( show i ∈ Finset.image ( fun j : Fin J.card => J.orderEmbOfFin rfl j ) Finset.univ from by aesop ) ; aesop;
    · exact fun h i => h _ ( Finset.orderEmbOfFin_mem _ _ _ )
