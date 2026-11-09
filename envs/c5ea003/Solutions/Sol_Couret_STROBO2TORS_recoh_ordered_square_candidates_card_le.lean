-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_ordered_square_candidates_card_le
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:55:37.562481+00:00
-- url     : https://prove2.me/submissions/1098cfce-c9c9-42fd-9faf-ae7f12c4da58

import Aesop
import Definitions.Def_Couret_RecohDecoderBounds_60ec29457baa
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_double_fibre_eq_translate
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_support_card_le_six
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6

set_option autoImplicit false

/-!
Finite combinatorial bounds for the RECOH candidate decoder.

Each possible three-element edge set E contributes either no half-sum or a
coset of the actual subgroup G[2].  The general counting bound is the number
of edge sets times |G[2]|.  The numerical factor twenty is used only when
the observed square has support of cardinality at most six; this hypothesis
is proved for the ordered square of an actual three-element support.

These are cardinality statements about the finite candidate specification.
They do not by themselves assert a running-time bound for its implementation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



@[simp]
theorem recoh_mem_double_fibre (t sigma : G) :
    sigma ∈ recohDoubleFibre t ↔ sigma + sigma = t := by
  simp [recohDoubleFibre]



/-- The zero fibre counts the actual two-torsion subgroup used in the
optimal-bank statements. -/
theorem recoh_double_fibre_zero_card :
    (recohDoubleFibre (0 : G)).card =
      Nat.card (recohTorsionSubgroup (G := G) 2) := by
  classical
  letI : Fintype (recohTorsionSubgroup (G := G) 2) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  change (Finset.univ.filter (fun x : G => x + x = 0)).card =
    Fintype.card {x : G // x ∈ recohTorsionSubgroup (G := G) 2}
  rw [Fintype.card_subtype]
  simp only [recoh_mem_torsion_subgroup, two_nsmul]

/-- Every nonempty doubling fibre has exactly `|G[2]|` elements. -/
theorem recoh_double_fibre_card_of_nonempty (t : G)
    (ht : (recohDoubleFibre t).Nonempty) :
    (recohDoubleFibre t).card =
      Nat.card (recohTorsionSubgroup (G := G) 2) := by
  obtain ⟨sigma, hsigma⟩ := ht
  rw [recoh_double_fibre_eq_translate t sigma
    ((recoh_mem_double_fibre _ _).mp hsigma), translateSupport_card,
    recoh_double_fibre_zero_card]

/-- A doubling fibre has cardinality either zero or `|G[2]|`. -/
theorem recoh_double_fibre_card_zero_or_torsion (t : G) :
    (recohDoubleFibre t).card = 0 ∨
      (recohDoubleFibre t).card =
        Nat.card (recohTorsionSubgroup (G := G) 2) := by
  by_cases ht : (recohDoubleFibre t).Nonempty
  · exact Or.inr (recoh_double_fibre_card_of_nonempty t ht)
  · exact Or.inl (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ht))

/-- The bound applies to every doubling fibre, including empty ones. -/
theorem recoh_double_fibre_card_le (t : G) :
    (recohDoubleFibre t).card ≤
      Nat.card (recohTorsionSubgroup (G := G) 2) := by
  rcases recoh_double_fibre_card_zero_or_torsion t with hzero | hcard
  · rw [hzero]
    exact Nat.zero_le _
  · exact hcard.le

omit [AddCommGroup G] [DecidableEq G] in
/-- At most twenty edge sets are considered when the observed square has
support of cardinality at most six.  No validity of `R` is otherwise assumed. -/
theorem recoh_edge_sets_card_le_twenty (R : G → ℕ)
    (hR : (recohSquareSupport R).card ≤ 6) :
    ((recohSquareSupport R).powersetCard 3).card ≤ 20 := by
  rw [Finset.card_powersetCard]
  calc
    (recohSquareSupport R).card.choose 3 ≤ Nat.choose 6 3 :=
      Nat.choose_le_choose 3 hR
    _ = 20 := by decide

/-- Exact fibrewise count of the edge-set/half-sum pairs. -/
theorem recoh_candidate_pairs_card_eq_sum (R : G → ℕ) :
    (recohCandidatePairs R).card =
      ∑ E ∈ (recohSquareSupport R).powersetCard 3,
        (recohDoubleFibre (E.sum id)).card := by
  simp only [recohCandidatePairs, recohDoubleFibre, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

/-- General bound for arbitrary observations: each edge set contributes
at most `|G[2]|` candidate pairs. -/
theorem recoh_candidate_pairs_card_le_edges_mul_torsion (R : G → ℕ) :
    (recohCandidatePairs R).card ≤
      ((recohSquareSupport R).powersetCard 3).card *
        Nat.card (recohTorsionSubgroup (G := G) 2) := by
  rw [recoh_candidate_pairs_card_eq_sum]
  calc
    (∑ E ∈ (recohSquareSupport R).powersetCard 3,
        (recohDoubleFibre (E.sum id)).card) ≤
      ∑ _E ∈ (recohSquareSupport R).powersetCard 3,
        Nat.card (recohTorsionSubgroup (G := G) 2) := by
          exact Finset.sum_le_sum (fun E _ => recoh_double_fibre_card_le (E.sum id))
    _ = ((recohSquareSupport R).powersetCard 3).card *
        Nat.card (recohTorsionSubgroup (G := G) 2) := by simp

/-- With at most six observed square positions there are at most
`20 * |G[2]|` candidate pairs. -/
theorem recoh_candidate_pairs_card_le_twenty_mul_torsion (R : G → ℕ)
    (hR : (recohSquareSupport R).card ≤ 6) :
    (recohCandidatePairs R).card ≤
      20 * Nat.card (recohTorsionSubgroup (G := G) 2) := by
  exact (recoh_candidate_pairs_card_le_edges_mul_torsion R).trans
    (Nat.mul_le_mul_right _ (recoh_edge_sets_card_le_twenty R hR))

/-- Passing from candidate pairs to their decoded supports cannot increase
cardinality; the same numerical bound therefore holds for candidates. -/
theorem recoh_candidates_card_le_twenty_mul_torsion (R : G → ℕ)
    (hR : (recohSquareSupport R).card ≤ 6) :
    (recohCandidates R).card ≤
      20 * Nat.card (recohTorsionSubgroup (G := G) 2) := by
  exact Finset.card_image_le.trans
    (recoh_candidate_pairs_card_le_twenty_mul_torsion R hR)



/-- The corresponding bound for decoded supports of a genuine observation. -/
theorem p2m_local_recoh_ordered_square_candidates_card_le (S : Finset G)
    (hS : S.card = 3) :
    (recohCandidates (orderedSquare S)).card ≤
      20 * Nat.card (recohTorsionSubgroup (G := G) 2) := by
  exact recoh_candidates_card_le_twenty_mul_torsion (orderedSquare S)
    (recoh_square_support_card_le_six S hS)

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
        (@Couret.STROBO2TORS.recohCandidates.{p2m_u_0} G inst inst_1 inst_2
          (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
        (Nat.card.{p2m_u_0}
          (@Subtype.{p2m_u_0 + 1} G fun x =>
            @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              x))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_ordered_square_candidates_card_le

