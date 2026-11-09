-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_canonical_terms_fixed
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:57.518488+00:00
-- url     : https://prove2.me/submissions/f16d6194-be96-44e0-afbc-b8edfea0f514

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





theorem recoh_canonical_terms_nodup_keys (ts : RecohSparseTerms)
    (ht : RecohCanonicalTerms ts) : (ts.map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact ht.1.imp (fun h => Nat.ne_of_lt h)



private theorem recoh_sparse_coeff_at_mem_of_nodup
    (ts : RecohSparseTerms) (hkeys : (ts.map Prod.fst).Nodup)
    (t : ℕ × ℤ) (ht : t ∈ ts) : recohSparseCoeff ts t.1 = t.2 := by
  induction ts with
  | nil => simp at ht
  | cons a ts ih =>
    obtain ⟨ha, hk⟩ := List.nodup_cons.mp hkeys
    rcases List.mem_cons.mp ht with rfl | ht
    · have hz := recoh_sparse_coeff_zero_of_not_mem ts t.1 ha
      change (if t.1 = t.1 then t.2 else 0) + recohSparseCoeff ts t.1 = _
      simp only [if_true, hz, add_zero]
    · have hne : a.1 ≠ t.1 := by
        intro he
        apply ha
        exact List.mem_map.mpr ⟨t, ht, he.symm⟩
      change (if a.1 = t.1 then a.2 else 0) + recohSparseCoeff ts t.1 = _
      rw [if_neg hne, zero_add]
      exact ih hk ht

theorem p2m_local_recoh_canonical_terms_fixed (ts : RecohSparseTerms)
    (ht : RecohCanonicalTerms ts) : recohCanonicalizeTerms ts = ts := by
  have hk := recoh_canonical_terms_nodup_keys ts ht
  have hs : recohActiveExponents ts = (ts.map Prod.fst).toFinset := by
    ext n
    simp only [recoh_mem_active_exponents, List.mem_toFinset]
    constructor
    · intro hn
      by_contra hnot
      exact hn (recoh_sparse_coeff_zero_of_not_mem ts n hnot)
    · intro hn
      obtain ⟨t, hmem, rfl⟩ := List.mem_map.mp hn
      rw [recoh_sparse_coeff_at_mem_of_nodup ts hk t hmem]
      exact ht.2 t hmem
  have hsort : ((ts.map Prod.fst).toFinset.sort (· ≤ ·)) = ts.map Prod.fst := by
    apply (List.toFinset_sort (· ≤ ·) hk).mpr
    rw [List.pairwise_map]
    exact ht.1.imp (fun h => Nat.le_of_lt h)
  rw [recohCanonicalizeTerms, hs, hsort, List.map_map]
  change ts.map (fun t => (t.1, recohSparseCoeff ts t.1)) = ts
  calc
    ts.map (fun t => (t.1, recohSparseCoeff ts t.1)) = ts.map id := by
      apply List.map_congr_left
      intro t hm
      exact Prod.ext rfl (recoh_sparse_coeff_at_mem_of_nodup ts hk t hm)
    _ = ts := List.map_id ts





















































end Couret.STROBO2TORS

theorem solution : ∀ (ts : Couret.STROBO2TORS.RecohSparseTerms),
  Couret.STROBO2TORS.RecohCanonicalTerms ts →
    @Eq.{1} Couret.STROBO2TORS.RecohSparseTerms (Couret.STROBO2TORS.recohCanonicalizeTerms ts) ts := @_root_.Couret.STROBO2TORS.p2m_local_recoh_canonical_terms_fixed

