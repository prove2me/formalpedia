-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_canonical_two_overlap_pairs_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:51.020429+00:00
-- url     : https://prove2.me/submissions/2908db24-0ab8-43d7-ace4-fc9c561c2b39

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_canonical_root_terms_eq_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_canonical_root_terms_eq_neg_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_overlap_index_pairs_empty_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_eq_or_neg_of_square_eq
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



theorem recoh_literal_sign_overlap_iff (left right : I → RecohSparseTerms) :
    recohLiteralSignOverlap left right = true ↔
      ∀ i, left i = right i ∨ left i = recohNegateTerms (right i) := by
  simp [recohLiteralSignOverlap]

end LiteralComparison

section IndexedPairs

variable {A : Type*}









end IndexedPairs

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]



theorem recoh_canonical_primary_terms_eq_iff (p : ℕ) [Fact p.Prime]
    (i : RecohPrimaryCoordinate q p)
    (S T : Finset ((j : Fin d) → ZMod (q j))) :
    recohCanonicalPrimaryTerms q p i S = recohCanonicalPrimaryTerms q p i T ↔
      recohSupportProbe (recohCyclicPrimaryBank q p (recohCanonicalPrimaryData q p) i) S =
        recohSupportProbe (recohCyclicPrimaryBank q p (recohCanonicalPrimaryData q p) i) T := by
  letI : NeZero (p ^ ((recohCanonicalPrimaryData q p).exponent i + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [recohCanonicalPrimaryTerms, recohCanonicalPrimaryTerms,
    recoh_canonical_root_terms_eq_iff (Fact.out : p.Prime) _ (recoh_cyclic_root_primitive _),
    recoh_cyclic_primary_bank_interpret q p (recohCanonicalPrimaryData q p) i S,
    recoh_cyclic_primary_bank_interpret q p (recohCanonicalPrimaryData q p) i T]

theorem recoh_canonical_primary_terms_eq_neg_iff (p : ℕ) [Fact p.Prime]
    (i : RecohPrimaryCoordinate q p)
    (S T : Finset ((j : Fin d) → ZMod (q j))) :
    recohCanonicalPrimaryTerms q p i S =
        recohNegateTerms (recohCanonicalPrimaryTerms q p i T) ↔
      recohSupportProbe (recohCyclicPrimaryBank q p (recohCanonicalPrimaryData q p) i) S =
        -recohSupportProbe (recohCyclicPrimaryBank q p (recohCanonicalPrimaryData q p) i) T := by
  letI : NeZero (p ^ ((recohCanonicalPrimaryData q p).exponent i + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [recohCanonicalPrimaryTerms, recohCanonicalPrimaryTerms,
    recoh_canonical_root_terms_eq_neg_iff (Fact.out : p.Prime) _ (recoh_cyclic_root_primitive _),
    recoh_cyclic_primary_bank_interpret q p (recohCanonicalPrimaryData q p) i S,
    recoh_cyclic_primary_bank_interpret q p (recohCanonicalPrimaryData q p) i T]







theorem recoh_canonical_two_overlap_iff
    (S T : Finset ((j : Fin d) → ZMod (q j))) :
    recohCanonicalTwoOverlap q S T = true ↔
      ∀ i : RecohEvenCoordinate q,
        recohSupportProbe (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i) S =
          recohSupportProbe (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i) T ∨
        recohSupportProbe (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i) S =
          -recohSupportProbe (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i) T := by
  simp only [recohCanonicalTwoOverlap, recoh_literal_sign_overlap_iff,
    recoh_canonical_primary_terms_eq_iff, recoh_canonical_primary_terms_eq_neg_iff]



/-- Equal ordered squares imply a positive literal overlap test.  Unlike
the separate nonzero guard, this theorem needs no triple cardinality. -/
theorem recoh_canonical_two_overlap_of_square_eq
    (S T : Finset ((j : Fin d) → ZMod (q j)))
    (hsquare : orderedSquare S = orderedSquare T) :
    recohCanonicalTwoOverlap q S T = true := by
  apply (recoh_canonical_two_overlap_iff q S T).mpr
  intro i
  exact recoh_support_probe_eq_or_neg_of_square_eq
    (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2) i) S T
    (fun z => congrFun hsquare z)



/-- The empty-overlap branch used before looking for a ternary coordinate
is exact on a list of representatives in one realized square fibre. -/
theorem p2m_local_recoh_canonical_two_overlap_pairs_empty_iff
    (xs : List (Finset ((j : Fin d) → ZMod (q j))))
    (R : ((j : Fin d) → ZMod (q j)) → ℕ)
    (h : ∀ S ∈ xs, orderedSquare S = R) :
    recohOverlapIndexPairs xs (recohCanonicalTwoOverlap q) = ∅ ↔ xs.length ≤ 1 := by
  apply recoh_overlap_index_pairs_empty_iff
  intro S hS T hT
  exact recoh_canonical_two_overlap_of_square_eq q S T ((h S hS).trans (h T hT).symm)

end Cyclic

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (xs : List.{0} (Finset.{0} ((j : Fin d) → ZMod (q j)))) (R : ((j : Fin d) → ZMod (q j)) → Nat),
  (∀ (S : Finset.{0} ((j : Fin d) → ZMod (q j))),
      @Membership.mem.{0, 0} (Finset.{0} ((j : Fin d) → ZMod (q j))) (List.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))))
          (@List.instMembership.{0} (Finset.{0} ((j : Fin d) → ZMod (q j)))) xs S →
        @Eq.{1} (((j : Fin d) → ZMod (q j)) → Nat)
          (@Couret.STROBO2TORS.orderedSquare.{0} ((j : Fin d) → ZMod (q j))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            S)
          R) →
    Iff
      (@Eq.{1}
        (Finset.{0}
          (Prod.{0, 0} (Fin (@List.length.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))) xs))
            (Fin (@List.length.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))) xs))))
        (@Couret.STROBO2TORS.recohOverlapIndexPairs.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))) xs
          (@Couret.STROBO2TORS.recohCanonicalTwoOverlap d q inst))
        (@EmptyCollection.emptyCollection.{0}
          (Finset.{0}
            (Prod.{0, 0} (Fin (@List.length.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))) xs))
              (Fin (@List.length.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))) xs))))
          (@Finset.instEmptyCollection.{0}
            (Prod.{0, 0} (Fin (@List.length.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))) xs))
              (Fin (@List.length.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))) xs))))))
      (@LE.le.{0} Nat instLENat (@List.length.{0} (Finset.{0} ((j : Fin d) → ZMod (q j))) xs)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_canonical_two_overlap_pairs_empty_iff

