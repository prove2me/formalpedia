-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_card_of_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:52.091914+00:00
-- url     : https://prove2.me/submissions/bb358d21-a171-4ca5-a8e8-f243d8dfb208

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_nonemptyFullFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_nonempty_of_four
import Theorems.Thm_Couret_STROBO2TORS_ordinary_exceptionalFibres_disjoint
import Theorems.Thm_Couret_STROBO2TORS_withoutZero_injective_on_nonemptyFullFibres
import Definitions.Def_Couret_Strobo2TorsZeroFreeAll_270e04a89080

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]

/-- If G[2] has at least four members, every ordinary complete fibre has a
nonempty zero-free restriction. This is stronger than a size formula:
there are no disappearing ordinary fibres. -/
theorem ordinaryNonemptyFibres_eq_ordinary_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (ordinaryNonemptyFibres : Finset (Finset (Finset G))) = ordinaryFibres := by
  unfold ordinaryNonemptyFibres
  ext F
  constructor
  · intro hF
    exact (Finset.mem_filter.mp hF).1
  · intro hF
    exact Finset.mem_filter.mpr
      ⟨hF, ordinaryFibres_nonempty_of_four hh F hF⟩





/-- For h ≥ 4, zero removal loses NO complete fibre of either type. The
image of restriction therefore has the same cardinality as all full fibres. -/
theorem nonemptyFullFibres_eq_all_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (nonemptyFullFibres : Finset (Finset (Finset G))) = allSquareFibres := by
  rw [nonemptyFullFibres_eq_union,
    ordinaryNonemptyFibres_eq_ordinary_of_four hh]
  exact (allSquareFibres_eq_union (G := G)).symm

/-- Count the complete surviving zero-free fibres before numerical
substitution: ordinary + exceptional, with no cross-type identifications. -/
theorem p2m_local_zeroFreeFullFibres_card_of_four
    (hh : 4 ≤ (twoTorsion : Finset G).card) :
    (zeroFreeFullFibres : Finset (Finset (Finset G))).card =
      (ordinaryFibres : Finset (Finset (Finset G))).card +
        (exceptionalFibres : Finset (Finset (Finset G))).card := by
  calc
    (zeroFreeFullFibres : Finset (Finset (Finset G))).card =
        (nonemptyFullFibres : Finset (Finset (Finset G))).card := by
          unfold zeroFreeFullFibres
          exact Finset.card_image_iff.mpr withoutZero_injective_on_nonemptyFullFibres
    _ = (allSquareFibres : Finset (Finset (Finset G))).card := by
      rw [nonemptyFullFibres_eq_all_of_four hh]
    _ = (ordinaryFibres : Finset (Finset (Finset G))).card +
          (exceptionalFibres : Finset (Finset (Finset G))).card := by
      rw [allSquareFibres_eq_union,
        Finset.card_union_of_disjoint ordinary_exceptionalFibres_disjoint]





end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2))
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_card_of_four

