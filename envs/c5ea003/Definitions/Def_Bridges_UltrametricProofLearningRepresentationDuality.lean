-- Prove2me | Definitions.Def_Bridges_UltrametricProofLearningRepresentationDuality
-- name    : Bridges_UltrametricProofLearningRepresentationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:58.621263+00:00
-- url     : https://prove2.me/theorems/f3af66e6-1a16-4e63-bda2-eecd0b464cc4
-- title:
--   Aether Catalog definitions — Bridges_UltrametricProofLearningRepresentationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricProofLearningRepresentationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricProofLearningRepresentationDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ultrametric Proof-Learning Representation Duality via Observer Semimodules

This file formalizes a **finite duality principle for proof dynamics**: a proof-learning
system with ultrametric contraction and observer-stable compression is *completely
recoverable* from a finite observer evaluation semimodule, and conversely the semimodule
algorithmically reconstructs a canonical sparse predictor tree with a correctness
certificate.

## Main Results

### Definitions (12 novel)
* `evalProfile` — observer evaluation map: compress then observe
* `ObserverSeparatesCompressed` — observers distinguish distinct compressed states
* `RealizableProfiles` — image of the observer evaluation map
* `CompressedUltrametric` — ultrametric compatible with compression
* `UltrametricProofSystem` — full proof-learning system bundle
* `evalProfileOnRange` — restriction of evalProfile to compressed states
* `compressedProfileEquiv` — the finite duality equivalence
* `profileSup`, `profileLE` — tropical/idempotent semimodule operations
* `ultraBallRel` — ultrametric ball equivalence relation
* `RootedTreeModel` — hierarchical predictor tree model
* `CertifiedPredictor` — predictor with correctness certificate
* `thresholdSublevel` — spectral filtration by observer thresholds

### Theorems (20+)
* `evalProfile_injective_on_compressed` — injectivity on fixed points (Thm A)
* `evalProfile_factors_through_C` — factorization through compression
* `evalProfile_injective_on_range` — injectivity on range C
* `evalProfileOnRange_injective/surjective` — bijection components
* `compressedProfileEquiv` — finite duality equivalence (Thm A')
* `card_realizable_profiles_eq_card_compressed` — cardinality matching
* `exists_canonical_ultrametric_tree` — tree reconstruction (Thm B)
* `canonical_tree_cluster_equiv` — clusters are equivalence relations
* `canonical_tree_unique` — uniqueness up to equivalence (Thm B')
* `certified_trace_reconstruction` — trace-based reconstruction (Thm C')
* `observer_separation_implies_faithful_encoding` — bridge to diagonal avoidance
* `profileSup_comm/assoc/idem` — semimodule algebraic laws
* `thresholdSublevel_mono` — spectral filtration monotonicity
* `finite_observer_representation_duality` — master theorem

## Bridge Architecture

Mirrors `certified_gibbs_reconstruction_from_boundary_partition`:
- Boundary data = observer profiles
- Partition = ultrametric cluster partition
- Reconstruction = profile → compressed state via equivalence inverse
- Certificate = observer evaluation recovery

## Application Keywords

ultrametric learning, proof-state compression, observer semimodules, idempotent algebra,
tropical representation theory, hierarchical predictor reconstruction, dendrogram
certification, symbolic machine learning, prime-congruence spectra, proof dynamics,
certified latent structure extraction
-/


open Function Set Finset

noncomputable section

namespace UltrametricProofLearning

/-! ## §1. Core Definitions -/

/-- Idempotence of a self-map: `C (C x) = C x` for all `x`. -/
def IsIdempotent {S : Type*} (C : S → S) : Prop := ∀ x, C (C x) = C x

/-- The observer evaluation map: compress first, then observe.
    `evalProfile C obs x i = obs i (C x)` -/
def evalProfile {S ι σ : Type*} (C : S → S) (obs : ι → S → σ) : S → (ι → σ) :=
  fun x i => obs i (C x)

/-- Observer separation on compressed states: observers distinguish all distinct
    compressed (fixed-point) states. -/
def ObserverSeparatesCompressed {S ι σ : Type*}
    (C : S → S) (obs : ι → S → σ) : Prop :=
  ∀ ⦃x y : S⦄, C x = x → C y = y →
    (∀ i, obs i x = obs i y) → x = y




/-! ## §2. Theorem A — Faithful Finite Observer Representation -/




/-! ## §3. Theorem A' — Finite Duality (Compressed States ≃ Profiles) -/

/-- The evaluation map from `Set.range C` to `Set.range (evalProfile C obs)`. -/
def evalProfileOnRange
    {S ι σ : Type*}
    (C : S → S) (obs : ι → S → σ)
    (_h_idem : IsIdempotent C) :
    Set.range C → Set.range (evalProfile C obs) :=
  fun ⟨x, _hx⟩ => ⟨evalProfile C obs x, x, rfl⟩

/-- The evaluation map on range is surjective. -/
theorem evalProfileOnRange_surjective
    {S ι σ : Type*}
    (C : S → S) (obs : ι → S → σ)
    (h_idem : IsIdempotent C) :
    Surjective (evalProfileOnRange C obs h_idem) := by
  intro ⟨f, hf⟩
  obtain ⟨x, rfl⟩ := hf
  refine ⟨⟨C x, ⟨x, rfl⟩⟩, ?_⟩
  simp only [evalProfileOnRange, Subtype.mk.injEq]
  ext i; simp only [evalProfile]; congr 1; exact h_idem x

/-- The evaluation map on range is injective (from observer separation). -/
theorem evalProfileOnRange_injective
    {S ι σ : Type*}
    (C : S → S) (obs : ι → S → σ)
    (h_idem : IsIdempotent C)
    (h_sep : ObserverSeparatesCompressed C obs) :
    Injective (evalProfileOnRange C obs h_idem) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp only [evalProfileOnRange, Subtype.mk.injEq] at h
  simp only [Subtype.mk.injEq]
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  apply h_sep (h_idem a) (h_idem b)
  intro i
  have := congr_fun h i
  simp only [evalProfile] at this
  rwa [h_idem, h_idem] at this

/-- **Theorem A' (Finite Observer Duality — Constructive).**
    The evaluation map induces an equivalence between compressed states and
    realizable profiles. This is the central duality theorem: compressed proof
    states biject with observer profiles through the evaluation map. -/
def compressedProfileEquiv
    {S ι σ : Type*}
    (C : S → S) (obs : ι → S → σ)
    (h_idem : IsIdempotent C)
    (h_sep : ObserverSeparatesCompressed C obs) :
    Set.range C ≃ Set.range (evalProfile C obs) :=
  Equiv.ofBijective
    (evalProfileOnRange C obs h_idem)
    ⟨evalProfileOnRange_injective C obs h_idem h_sep,
     evalProfileOnRange_surjective C obs h_idem⟩



/-! ## §4. Tropical Semimodule Structure on Profiles -/

/-- Pointwise sup on observer profiles: the tropical/idempotent addition. -/
def profileSup {ι σ : Type*} [Max σ] (f g : ι → σ) : ι → σ :=
  fun i => max (f i) (g i)




/-- Pointwise order on profiles. -/
def profileLE {ι σ : Type*} [LE σ] (f g : ι → σ) : Prop :=
  ∀ i, f i ≤ g i




/-! ## §5. Ultrametric Cluster Structure -/

/-- The ultrametric ball relation at radius `r`:
    `x ~ y` iff `d(x,y) ≤ r`. -/
def ultraBallRel {S : Type*} (d : S → S → ℝ) (r : ℝ) : S → S → Prop :=
  fun x y => d x y ≤ r






/-! ## §6. Theorem B — Canonical Ultrametric Tree Reconstruction -/

/-- A rooted tree model for hierarchical predictor reconstruction. -/
structure RootedTreeModel (S : Type*) where
  /-- The set of leaves -/
  leaves : Set S
  /-- Cluster relation: `sameCluster x y r` means x, y in same cluster at radius r -/
  sameCluster : S → S → ℝ → Prop
  /-- The root radius -/
  rootRadius : ℝ

/-- Construct the canonical tree model from a compressed ultrametric. -/
def canonicalTreeModel {S : Type*}
    (C : S → S) (d : S → S → ℝ) : RootedTreeModel S where
  leaves := Set.range C
  sameCluster := fun x y r => d (C x) (C y) ≤ r
  rootRadius := 0



/-! ## §7. Theorem B' — Uniqueness Up to Cluster Equivalence -/

/-- Two tree models are cluster-equivalent if they agree on all cluster relations. -/
def TreeModelsEquiv {S : Type*}
    (T₁ T₂ : RootedTreeModel S) (_C : S → S) : Prop :=
  ∀ x y r, T₁.sameCluster x y r ↔ T₂.sameCluster x y r


/-! ## §8. Certified Predictor Structures -/

/-- A certified predictor model. -/
structure CertifiedPredictor (S ι σ : Type*) where
  /-- Prediction from profile to state -/
  predict : (ι → σ) → S
  /-- The compression operator -/
  compress : S → S
  /-- The observer family -/
  observe : ι → S → σ

/-- A certified predictor is correct if predicting from a compressed profile
    yields a state with the same profile. -/
def CertifiedPredictor.IsCorrect {S ι σ : Type*}
    (P : CertifiedPredictor S ι σ) : Prop :=
  ∀ x : S, evalProfile P.compress P.observe
    (P.predict (evalProfile P.compress P.observe x)) =
    evalProfile P.compress P.observe x


/-! ## §9. Trace-Based Reconstruction -/

/-- Extract the compressed states from a trace. -/
def traceCompressedStates {S : Type*} [DecidableEq S]
    (C : S → S) (trace : List S) : Finset S :=
  (trace.map C).toFinset



/-! ## §10. Bridge Lemmas -/



/-! ## §11. Finite Cardinality Bounds -/



/-! ## §12. Spectral Filtration -/

/-- Threshold sublevel set: states with all observer scores ≤ threshold. -/
def thresholdSublevel {S ι σ : Type*} [LE σ]
    (C : S → S) (obs : ι → S → σ) (t : ι → σ) : Set S :=
  {x | ∀ i, obs i (C x) ≤ t i}



/-! ## §13. Master Theorem -/


end UltrametricProofLearning


