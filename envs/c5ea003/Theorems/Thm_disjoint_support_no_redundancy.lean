-- Prove2me | Theorems.Thm_disjoint_support_no_redundancy
-- name    : disjoint_support_no_redundancy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:30:32.285751+00:00
-- url     : https://prove2.me/theorems/843c8e1b-df1e-4da6-a4b0-3ea211631b8d
-- title:
--   Support rigidity theorem.
-- statement:
--   **Support rigidity theorem.** When generators have pairwise disjoint and
--       nontrivial supports, no generator can be expressed as the pointwise minimum
--       of shifted copies of the others.
--
--   ```lean
--   theorem disjoint_support_no_redundancy    {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
--       (hn : 0 < n)
--       (F : Fin n → V → ℤ)
--       (hdisjoint : PairwiseDisjointSupports F)
--       (hnontrivial : ∀ j : Fin n, ∃ v w : V,
--         v ∈ FunSupport (F j) ∧ w ∈ FunSupport (F j) ∧ F j v ≠ F j w)
--       (j : Fin n) (hn1 : 1 < n)
--       (hne : ∃ i : Fin n, i ≠ j)
--       (hfilt_ne : (Finset.univ.filter (· ≠ j) : Finset (Fin n)).Nonempty) :
--       ¬∃ (c : Fin n → ℤ),
--         ∀ v : V, F j v =
--           (Finset.univ.filter (· ≠ j)).inf' hfilt_ne
--             (fun i => F i v + c i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/LFunctions/TropicalKernelRigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/LFunctions/TropicalKernelRigidity.lean#L112

-- Thm stub generated from Bridges/LFunctions/TropicalKernelRigidity.lean
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



/-! ## Section 4: Disjoint Support Implies Irredundancy -/

theorem disjoint_support_no_redundancy    {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
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
          (fun i => F i v + c i) := by sorry
