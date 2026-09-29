-- Prove2me | solution 1 for right_mul_closed_eq_univ_cert
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:11:23.258679+00:00
-- url     : https://prove2.me/submissions/85f41d36-3310-4ffb-a85f-0003152957fc

-- Sol generated from Bridges/HilbertSpace/AlgorithmicSpectralCertification.lean
import Mathlib
import Definitions.Def_Bridges_HilbertSpace_AlgorithmicSpectralCertification
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Algorithmic Spectral Certification for Cayley Graphs

This file develops a theory of **algorithmically certifiable spectral expansion**
for Cayley graphs of finite groups, with focus on `GL₂(𝔽_q)`.

The central paradigm is **expansion by local algebraic witnesses**: sparse
algebraic fingerprints — generation, irreducibility, determinant primitivity —
are efficiently checkable and certify spectral gap.

## Main results

* `algorithmic_certificate_sound_qualitative`: Soundness — certificate data
  implies no nontrivial harmonic mean-zero functions (spectral gap > 0).
* `certificate_components_decidable`: Decidability of certificate predicates.
* `generation_implies_harmonic_triviality`: Generation ⟹ spectral gap.
* `l2_mixing_decay_certified`: Cross-domain bridge — contraction ⟹ mixing.
* `irred_charpoly_not_split_torus`: Algebraic fingerprint theorem.
* `primitive_det_surjective_image`: Determinant primitivity theorem.
* `avgOperator_norm_le_one_cert`: L² operator norm bound ≤ 1.
* `master_certificate_pipeline`: Master theorem chaining the full pipeline.

## References

* Lubotzky (1994). Discrete Groups, Expanding Graphs and Invariant Measures.
* Hoory, Linial, Wigderson (2006). Expander Graphs and their Applications.
* Bourgain, Gamburd (2008). Uniform expansion bounds for Cayley graphs of SL₂(𝔽_p).
-/


open Finset BigOperators

/-! ## Section 1: Core Definitions -/







/-! ## Section 2: Spectral Certificate Data -/





/-! ## Section 3: Symmetric Generator Properties -/




/-! ## Section 4: Maximum Principle -/





/-! ## Section 5: L² Operator Norm Bound -/

/-
**Theorem: L² operator norm ≤ 1.** The averaging operator does not increase
the L² norm. This is a consequence of Jensen's inequality.
-/

/-! ## Section 6: Theorem 1 — Soundness of Algorithmic Certification -/


/-! ## Section 7: Theorem 2 — Decidability -/


/-! ## Section 8: Theorem 3 — Generation Implies Harmonic Triviality -/


/-! ## Section 9: Theorem 4 — Mixing Time Bound (Cross-Domain Bridge) -/




/-! ## Section 10: Algebraic Fingerprint Theorems -/



/-! ## Section 11: Primitive Determinant -/



/-! ## Section 12: Certification Density Conjecture -/


/-! ## Section 13: Master Certificate Pipeline -/


theorem solution{G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (S : Finset G) (A : Finset G)
    (hgen : Subgroup.closure (↑S : Set G) = ⊤)
    (hA : A.Nonempty)
    (hclosed : ∀ a ∈ A, ∀ s ∈ S, a * s ∈ A) :
    A = Finset.univ := by
  have h_stabilizer : ∀ g : G, g ∈ Subgroup.closure (S : Set G) → ∀ a ∈ A, a * g ∈ A := by
    refine' fun g hg => Subgroup.closure_induction _ _ _ _ hg
    · exact fun s hs a ha => hclosed a ha s hs
    · simp
    · exact fun x y _ _ hx' hy' a ha => by simpa only [mul_assoc] using hy' _ (hx' _ ha)
    · intro x _ hx' a ha
      have h_inv : Finset.image (fun b => b * x) A = A :=
        Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hx')
          (by rw [Finset.card_image_of_injective _ fun a b h => mul_right_cancel h])
      replace h_inv := Finset.ext_iff.mp h_inv a; aesop
  simp_all +decide [Subgroup.eq_top_iff']
  exact Finset.eq_univ_of_forall fun g => by
    obtain ⟨a, ha⟩ := hA; simpa using h_stabilizer (a⁻¹ * g) a ha
