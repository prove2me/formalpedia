-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_canonicalize_terms_negate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:26:57.647425+00:00
-- url     : https://prove2.me/submissions/23f73bde-b94f-4537-ba61-f00925151ee2

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_negate_terms_polynomial
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





































theorem recoh_sparse_coeff_negate (ts : RecohSparseTerms) (n : ℕ) :
    recohSparseCoeff (recohNegateTerms ts) n = -recohSparseCoeff ts n := by
  rw [← recoh_terms_polynomial_coeff, recoh_negate_terms_polynomial,
    Polynomial.coeff_neg, recoh_terms_polynomial_coeff]

theorem p2m_local_recoh_canonicalize_terms_negate (ts : RecohSparseTerms) :
    recohCanonicalizeTerms (recohNegateTerms ts) =
      recohNegateTerms (recohCanonicalizeTerms ts) := by
  have hs : recohActiveExponents (recohNegateTerms ts) = recohActiveExponents ts := by
    ext n
    simp only [recoh_mem_active_exponents, recoh_sparse_coeff_negate, neg_ne_zero]
  unfold recohCanonicalizeTerms
  rw [hs]
  change _ = List.map (fun t => (t.1, -t.2))
    (List.map (fun n => (n, recohSparseCoeff ts n)) _)
  rw [List.map_map]
  apply List.map_congr_left
  intro n _
  exact Prod.ext rfl (recoh_sparse_coeff_negate ts n)

























end Couret.STROBO2TORS

theorem solution : ∀ (ts : Couret.STROBO2TORS.RecohSparseTerms),
  @Eq.{1} Couret.STROBO2TORS.RecohSparseTerms
    (Couret.STROBO2TORS.recohCanonicalizeTerms (Couret.STROBO2TORS.recohNegateTerms ts))
    (Couret.STROBO2TORS.recohNegateTerms (Couret.STROBO2TORS.recohCanonicalizeTerms ts)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_canonicalize_terms_negate

