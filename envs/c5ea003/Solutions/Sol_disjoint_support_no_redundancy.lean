-- Prove2me | solution 1 for disjoint_support_no_redundancy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:07:06.013979+00:00
-- url     : https://prove2.me/submissions/0b5ff76f-86d0-4a2c-8d2c-ba4cc2c4a726

-- Sol generated from Bridges/LFunctions/TropicalKernelRigidity.lean
import Mathlib
import Definitions.Def_Bridges_LFunctions_TropicalKernelRigidity
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Kernel Rigidity: Uniqueness of Generators up to Tropical Projective Equivalence

This file establishes a canonical-form theory for tropical kernel generators
of graph Laplacians. The central result is that under support-separation
hypotheses (pairwise disjoint supports), every minimal tropical generating
family is obtained from the canonical one by tropical projective equivalence:
permutation plus pointwise constant shifts.

## Main Definitions

* `TropProjEquiv` — tropical projective equivalence of indexed function families
* `FunSupport` — support of an integer-valued function (where it's nonzero)
* `PairwiseDisjointSupports` — family with pairwise disjoint supports
* `restrictedLaplacian'` — graph Laplacian restricted to a vertex subset
* `IsHarmonicOn` — S-harmonicity for graph functions
* `harmonicKernel` — set of S-harmonic functions

## Main Results

* `tropProjEquiv_refl` — tropical projective equivalence is reflexive
* `tropProjEquiv_symm` — tropical projective equivalence is symmetric
* `tropProjEquiv_trans` — tropical projective equivalence is transitive
* `min_on_disjoint_support` — support separation forces zeroes
* `disjoint_support_no_redundancy` — generators with disjoint supports are irredundant
* `disjoint_support_unique_up_to_tropProjEquiv` — main uniqueness theorem
* `harmonic_leaf_rigidity` — harmonic functions are rigid on leaves
* `same_support_implies_same_restricted_laplacian` — matroidal invariance
* `equilibrium_iff_harmonic` — bridge to discrete potential theory

## References

* Baker, M. and Norine, S. "Riemann–Roch and Abel–Jacobi theory on a
  finite graph" (2007)
* Develin, Santos, Sturmfels, "On the rank of a tropical matrix" (2005)
-/


open Finset BigOperators

/-! ## Section 1: Tropical Projective Equivalence -/





/-! ## Section 2: Function Support -/



/-! ## Section 3: Support Separation Lemmas -/

/-- For functions with disjoint supports, any function is zero outside
    its own support region. -/
theorem min_on_disjoint_support {ι V : Type*} [DecidableEq ι]
    (F : ι → V → ℤ)
    (hdisjoint : PairwiseDisjointSupports F)
    (i : ι) (v : V) (hv : v ∈ FunSupport (F i))
    (j : ι) (hj : j ≠ i) :
    F j v = 0 := by
  exact Classical.not_not.1 fun h => Set.disjoint_left.1 (hdisjoint j i hj) h hv


/-! ## Section 4: Disjoint Support Implies Irredundancy -/


/-! ## Section 5: Tropical Span on Disjoint Supports -/


/-! ## Section 6: Main Uniqueness Theorem -/

/-
**Helper.** The support-matching function is injective when supports are
    pairwise disjoint and nontrivial.
-/

/-
**Main uniqueness theorem.** Let `F G : Fin n → V → ℤ` be families with
    pairwise disjoint supports. If they have matching support structure and
    agree pointwise on matching supports, then they are tropically projectively
    equivalent (in fact with zero constants, i.e., equal up to permutation).

    This is the tropical analogue of basis uniqueness: under the combinatorial
    separation hypothesis, generators are canonical up to reindexing.
-/

/-! ## Section 7: Graph-Theoretic Specialization -/









/-! ## Section 8: Matroidal Invariance -/




/-! ## Section 9: Discrete Potential Theory Bridge -/




/-! ## Section 10: Falsifiable Conjecture -/


theorem solution    {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (hn : 0 < n)
    (F : Fin n → V → ℤ)
    (hdisjoint : PairwiseDisjointSupports F)
    (hnontrivial : ∀ j : Fin n, ∃ v w : V,
      v ∈ FunSupport (F j) ∧ w ∈ FunSupport (F j) ∧ F j v ≠ F j w)
    (j : Fin n) (hn1 : 1 < n)
    (hne : ∃ i : Fin n, i ≠ j)
    (hfilt_ne : (Finset.univ.filter (· ≠ j) : Finset (Fin n)).Nonempty) :
    ¬∃ (c : Fin n → ℤ),
      ∀ v : V, F j v =
        (Finset.univ.filter (· ≠ j)).inf' hfilt_ne
          (fun i => F i v + c i) := by
  intro ⟨c, hc⟩
  obtain ⟨v, w, hv, hw, hne⟩ := hnontrivial j
  have h_zero : ∀ i, i ≠ j → (F i v) = 0 ∧ (F i w) = 0 :=
    fun i hi => ⟨min_on_disjoint_support F hdisjoint j v hv i hi,
                 min_on_disjoint_support F hdisjoint j w hw i hi⟩
  have h_const : F j v = inf' ((Finset.univ : Finset (Fin n)).filter (fun x => x ≠ j))
      hfilt_ne (fun i => c i) ∧
      F j w = inf' ((Finset.univ : Finset (Fin n)).filter (fun x => x ≠ j))
      hfilt_ne (fun i => c i) := by
    simp_all +decide [Finset.inf'_eq_csInf_image]
    exact ⟨congr_arg _ (Set.image_congr fun i hi => by simp +decide [h_zero i hi]),
           congr_arg _ (Set.image_congr fun i hi => by simp +decide [h_zero i hi])⟩
  exact hne (h_const.1.trans h_const.2.symm)
