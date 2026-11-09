-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_canonicalize_terms_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:20.559661+00:00
-- url     : https://prove2.me/submissions/cee21764-a891-4a7d-b262-9a563f0803be

import Aesop
import Definitions.Def_Couret_RecohCanonicalCoefficients_7eb0bfadc07d
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

/-!
Canonical sparse integer coefficient lists.

The Python v0.2 `_terms` routine combines coefficients at equal exponents,
discards zeros, and sorts the remaining exponent/coefficient pairs.  The
definitions below express those operations on already typed lists.  Literal
equality and literal negation of the resulting lists are faithful to the
existing polynomial and complex-value semantics.  JSON parsing and Python
execution are not asserted by this file.
-/

namespace Couret.STROBO2TORS

open Polynomial















theorem recoh_mem_active_exponents (ts : RecohSparseTerms) (n : ℕ) :
    n ∈ recohActiveExponents ts ↔ recohSparseCoeff ts n ≠ 0 := by
  simp only [recohActiveExponents, Finset.mem_filter, List.mem_toFinset]
  constructor
  · exact And.right
  · intro hn
    refine ⟨?_, hn⟩
    by_contra hnot
    exact hn (recoh_sparse_coeff_zero_of_not_mem ts n hnot)













private theorem recoh_sparse_coeff_of_nodup_keys
    (keys : List ℕ) (f : ℕ → ℤ) (n : ℕ) (hkeys : keys.Nodup) :
    recohSparseCoeff (keys.map (fun e => (e, f e))) n =
      if n ∈ keys then f n else 0 := by
  induction keys with
  | nil => simp [recohSparseCoeff]
  | cons a keys ih =>
    obtain ⟨ha, hk⟩ := List.nodup_cons.mp hkeys
    simp only [List.map_cons, recohSparseCoeff, List.sum_cons]
    change (if a = n then f a else 0) +
      recohSparseCoeff (keys.map (fun e => (e, f e))) n = _
    rw [ih hk]
    by_cases h : a = n
    · subst a
      simp [ha]
    · simp [h, Ne.symm h]

theorem recoh_canonicalize_terms_coeff (ts : RecohSparseTerms) (n : ℕ) :
    recohSparseCoeff (recohCanonicalizeTerms ts) n = recohSparseCoeff ts n := by
  rw [recohCanonicalizeTerms,
    recoh_sparse_coeff_of_nodup_keys _ _ _ (Finset.sort_nodup _ _)]
  simp only [Finset.mem_sort, recoh_mem_active_exponents]
  split_ifs with hn
  · rfl
  · exact (not_ne_iff.mp hn).symm

theorem recoh_canonicalize_terms_polynomial (ts : RecohSparseTerms) :
    recohTermsPolynomial (recohCanonicalizeTerms ts) = recohTermsPolynomial ts := by
  apply Polynomial.ext
  intro n
  rw [recoh_terms_polynomial_coeff, recoh_terms_polynomial_coeff,
    recoh_canonicalize_terms_coeff]

theorem p2m_local_recoh_canonicalize_terms_eq_iff (xs ys : RecohSparseTerms) :
    recohCanonicalizeTerms xs = recohCanonicalizeTerms ys ↔
      recohTermsPolynomial xs = recohTermsPolynomial ys := by
  constructor
  · intro h
    simpa only [recoh_canonicalize_terms_polynomial] using
      congrArg recohTermsPolynomial h
  · intro h
    have hc : ∀ n, recohSparseCoeff xs n = recohSparseCoeff ys n := by
      intro n
      simpa only [recoh_terms_polynomial_coeff] using congrArg (fun P : ℤ[X] => P.coeff n) h
    have hs : recohActiveExponents xs = recohActiveExponents ys := by
      ext n
      simp only [recoh_mem_active_exponents, hc n]
    simp only [recohCanonicalizeTerms, hs]
    congr 1
    funext n
    rw [hc n]













































end Couret.STROBO2TORS

theorem solution : ∀ (xs ys : Couret.STROBO2TORS.RecohSparseTerms),
  Iff
    (@Eq.{1} Couret.STROBO2TORS.RecohSparseTerms (Couret.STROBO2TORS.recohCanonicalizeTerms xs)
      (Couret.STROBO2TORS.recohCanonicalizeTerms ys))
    (@Eq.{1} (@Polynomial.{0} Int Int.instSemiring) (Couret.STROBO2TORS.recohTermsPolynomial xs)
      (Couret.STROBO2TORS.recohTermsPolynomial ys)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_canonicalize_terms_eq_iff

