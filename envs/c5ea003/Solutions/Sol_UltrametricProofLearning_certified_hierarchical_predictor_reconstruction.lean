-- Prove2me | solution 1 for UltrametricProofLearning.certified_hierarchical_predictor_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:49:50.98366+00:00
-- url     : https://prove2.me/submissions/e94907f6-84e3-4822-be05-6c91a0bf7887

-- Sol generated from Bridges/UltrametricProofLearningRepresentationDuality.lean
import Mathlib
import Definitions.Def_Bridges_UltrametricProofLearningRepresentationDuality
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

open UltrametricProofLearning

/-! ## §1. Core Definitions -/







/-! ## §2. Theorem A — Faithful Finite Observer Representation -/


/-- The evaluation map factors through compression. -/
theorem evalProfile_factors_through_C
    {S ι σ : Type*}
    (C : S → S) (obs : ι → S → σ)
    (h_idem : IsIdempotent C) :
    ∀ x, evalProfile C obs x = evalProfile C obs (C x) := by
  intro x; ext i; unfold evalProfile; congr 1; exact (h_idem x).symm


/-! ## §3. Theorem A' — Finite Duality (Compressed States ≃ Profiles) -/







/-! ## §4. Tropical Semimodule Structure on Profiles -/









/-! ## §5. Ultrametric Cluster Structure -/







/-! ## §6. Theorem B — Canonical Ultrametric Tree Reconstruction -/





/-! ## §7. Theorem B' — Uniqueness Up to Cluster Equivalence -/



/-! ## §8. Certified Predictor Structures -/




/-! ## §9. Trace-Based Reconstruction -/




/-! ## §10. Bridge Lemmas -/



/-! ## §11. Finite Cardinality Bounds -/



/-! ## §12. Spectral Filtration -/




/-! ## §13. Master Theorem -/



open UltrametricProofLearning in
theorem solution    {S ι σ : Type*}
    [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    [DecidableEq σ] [Nonempty S]
    (C : S → S)
    (obs : ι → S → σ)
    (h_idem : IsIdempotent C)
    (_h_sep : ObserverSeparatesCompressed C obs) :
    ∃ (P : CertifiedPredictor S ι σ),
      P.compress = C ∧
      P.observe = obs ∧
      P.IsCorrect := by
  let predict : (ι → σ) → S := fun f =>
    if h : ∃ s : S, evalProfile C obs s = f then C h.choose
    else Classical.arbitrary S
  refine ⟨⟨predict, C, obs⟩, rfl, rfl, ?_⟩
  intro x
  show evalProfile C obs (predict (evalProfile C obs x)) = evalProfile C obs x
  simp only [predict]
  have hex : ∃ s : S, evalProfile C obs s = evalProfile C obs x := ⟨x, rfl⟩
  rw [dif_pos hex]
  rw [← evalProfile_factors_through_C C obs h_idem]
  exact hex.choose_spec
