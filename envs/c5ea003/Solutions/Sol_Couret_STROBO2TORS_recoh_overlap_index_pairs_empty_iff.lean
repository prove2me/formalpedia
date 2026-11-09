-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_overlap_index_pairs_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:41:35.093194+00:00
-- url     : https://prove2.me/submissions/0ef3e7c8-ce02-4af5-8e9d-8dc9535515e7

import Aesop
import Definitions.Def_Couret_RecohCanonicalOverlap_0d3ff2cb7fda
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCanonicalCoefficients_7eb0bfadc07d
import Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae

set_option autoImplicit false

/-!
Literal canonical coefficient comparisons and the binary overlap filter.

This module proves the typed mathematical meaning of Python v0.2's
`_two_overlaps`.  It does not formalize Python execution, tuple/list parsing,
the implementation of `combinations`, exceptions, or JSON serialization.
-/

namespace Couret.STROBO2TORS

section SignOrbits

variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2





end SignOrbits

section LiteralComparison

variable {I : Type*} [Fintype I]





end LiteralComparison

section IndexedPairs

variable {A : Type*}





/-- If every supplied pair overlaps, the filter keeps exactly all increasing
index pairs.  No ordering or distinctness of the values is assumed. -/
theorem recoh_overlap_index_pairs_all (xs : List A) (overlap : A → A → Bool)
    (h : ∀ a ∈ xs, ∀ b ∈ xs, overlap a b = true) :
    recohOverlapIndexPairs xs overlap = Finset.univ.filter (fun ij => ij.1 < ij.2) := by
  ext ij
  simp only [recohOverlapIndexPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_iff_left (h _ (List.getElem_mem _) _ (List.getElem_mem _))

/-- With all comparisons passing, an empty overlap set means that the
representative list has at most one entry. -/
theorem p2m_local_recoh_overlap_index_pairs_empty_iff (xs : List A) (overlap : A → A → Bool)
    (h : ∀ a ∈ xs, ∀ b ∈ xs, overlap a b = true) :
    recohOverlapIndexPairs xs overlap = ∅ ↔ xs.length ≤ 1 := by
  rw [recoh_overlap_index_pairs_all xs overlap h]
  constructor
  · intro hempty
    by_contra hn
    have hlen : 1 < xs.length := by omega
    let i : Fin xs.length := ⟨0, by omega⟩
    let j : Fin xs.length := ⟨1, hlen⟩
    have hmem : (i, j) ∈ Finset.univ.filter
        (fun ij : Fin xs.length × Fin xs.length => ij.1 < ij.2) := by
      simp [i, j]
    rw [hempty] at hmem
    simp at hmem
  · intro hlen
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ij hmem
    have hij := (Finset.mem_filter.mp hmem).2
    have hi := ij.1.isLt
    have hj := ij.2.isLt
    change ij.1.val < ij.2.val at hij
    omega

end IndexedPairs

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]























end Cyclic

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {A : Type p2m_u_0} (xs : List.{p2m_u_0} A) (overlap : A → A → Bool),
  (∀ (a : A),
      @Membership.mem.{p2m_u_0, p2m_u_0} A (List.{p2m_u_0} A) (@List.instMembership.{p2m_u_0} A) xs a →
        ∀ (b : A),
          @Membership.mem.{p2m_u_0, p2m_u_0} A (List.{p2m_u_0} A) (@List.instMembership.{p2m_u_0} A) xs b →
            @Eq.{1} Bool (overlap a b) Bool.true) →
    Iff
      (@Eq.{1} (Finset.{0} (Prod.{0, 0} (Fin (@List.length.{p2m_u_0} A xs)) (Fin (@List.length.{p2m_u_0} A xs))))
        (@Couret.STROBO2TORS.recohOverlapIndexPairs.{p2m_u_0} A xs overlap)
        (@EmptyCollection.emptyCollection.{0}
          (Finset.{0} (Prod.{0, 0} (Fin (@List.length.{p2m_u_0} A xs)) (Fin (@List.length.{p2m_u_0} A xs))))
          (@Finset.instEmptyCollection.{0}
            (Prod.{0, 0} (Fin (@List.length.{p2m_u_0} A xs)) (Fin (@List.length.{p2m_u_0} A xs))))))
      (@LE.le.{0} Nat instLENat (@List.length.{p2m_u_0} A xs)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_overlap_index_pairs_empty_iff

