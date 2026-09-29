-- Prove2me | solution 1 for harmonic_eq_const_cert
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:12.25944+00:00
-- url     : https://prove2.me/submissions/d92e6edd-d822-4f61-a7a4-72f3229247a4

-- Sol generated from Bridges/HilbertSpace/AlgorithmicSpectralCertification.lean
import Mathlib
import Definitions.Def_Bridges_HilbertSpace_AlgorithmicSpectralCertification
import Theorems.Thm_right_mul_closed_eq_univ_cert
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


/-- If `f(x) = max f` and `f(x) = avg_S f(x·s)`, then `f(x·s) = max f` for all s ∈ S. -/
theorem avg_eq_max_implies_nbrs_eq {G : Type*} [Group G] [Fintype G]
    (S : Finset G) (hS : S.Nonempty)
    (f : G → ℝ) (x : G) (M : ℝ)
    (hfx : f x = M)
    (hmax : ∀ y : G, f y ≤ M)
    (havg : f x = (↑S.card : ℝ)⁻¹ * ∑ s ∈ S, f (x * s)) :
    ∀ s ∈ S, f (x * s) = M := by
  by_contra h_contra
  have h_sum_lt : ∑ s ∈ S, f (x * s) < S.card * M := by
    simpa using Finset.sum_lt_sum (fun y _ => by linarith [hmax (x * y)])
      (show ∃ y ∈ S, f (x * y) < M from by
        push_neg at h_contra
        exact h_contra.imp fun y hy => ⟨hy.1, lt_of_le_of_ne (hmax _) hy.2⟩)
  rw [inv_mul_eq_div, eq_div_iff] at havg
    <;> nlinarith [show (S.card : ℝ) > 0 by exact Nat.cast_pos.mpr hS.card_pos]



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
    (S : Finset G) (hS : S.Nonempty)
    (_hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (↑S : Set G) = ⊤)
    (f : G → ℝ) (hf : IsHarmonicAS S f) :
    ∃ c : ℝ, ∀ x : G, f x = c := by
  obtain ⟨M, hM⟩ : ∃ M ∈ Set.range f, ∀ y ∈ Set.range f, y ≤ M :=
    ⟨Finset.max' (Set.toFinset (Set.range f))
      ⟨_, Set.mem_toFinset.mpr (Set.mem_range_self 1)⟩,
     Set.mem_toFinset.mp (Finset.max'_mem _ _),
     fun y hy => Finset.le_max' _ _ (Set.mem_toFinset.mpr hy)⟩
  set A := Finset.filter (fun x => f x = M) (Finset.univ : Finset G) with hA_def
  have hA_nonempty : A.Nonempty :=
    ⟨hM.1.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM.1.choose_spec⟩⟩
  have hA_closed : ∀ a ∈ A, ∀ s ∈ S, a * s ∈ A := by
    intros a ha s hs
    have h_eq : ∀ s ∈ S, f (a * s) = M :=
      avg_eq_max_implies_nbrs_eq S hS f a M
        (by aesop) (by aesop) (by aesop)
    aesop
  have hA_univ : A = Finset.univ :=
    right_mul_closed_eq_univ_cert S A hgen hA_nonempty hA_closed
  exact ⟨M, fun x => Finset.ext_iff.mp hA_univ x |> fun h => by aesop⟩
