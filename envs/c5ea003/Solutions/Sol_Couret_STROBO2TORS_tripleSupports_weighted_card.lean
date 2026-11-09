-- Prove2me | solution 1 for Couret.STROBO2TORS.tripleSupports_weighted_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:56.385934+00:00
-- url     : https://prove2.me/submissions/57e747c1-1692-4c86-b28a-13a91c4660dc

import Aesop
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_eq_union
import Theorems.Thm_Couret_STROBO2TORS_allSquareFibres_preimage
import Theorems.Thm_Couret_STROBO2TORS_exceptionalFibres_member_card
import Theorems.Thm_Couret_STROBO2TORS_ordinary_exceptionalFibres_disjoint
import Theorems.Thm_Couret_STROBO2TORS_tripleSupports_card
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















section Finite

variable [Fintype G]



















































































theorem p2m_local_tripleSupports_weighted_card :
    (Fintype.card G).choose 3 = (twoTorsion : Finset G).card *
      ((ordinaryFibres : Finset (Finset (Finset G))).card +
        2 * (exceptionalFibres : Finset (Finset (Finset G))).card) := by
  have hc : (tripleSupports : Finset (Finset G)).card =
      ∑ F ∈ (allSquareFibres (G := G)), F.card := by
    calc
      (tripleSupports : Finset (Finset G)).card =
          ∑ F ∈ (allSquareFibres (G := G)),
            ((tripleSupports (G := G)).filter (fun S => squareFibre S = F)).card :=
        Finset.card_eq_sum_card_image (squareFibre (G := G)) (tripleSupports (G := G))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro F hF; rw [allSquareFibres_preimage F hF]
  rw [tripleSupports_card, allSquareFibres_eq_union,
    Finset.sum_union ordinary_exceptionalFibres_disjoint] at hc
  have hO : (∑ F ∈ (ordinaryFibres (G := G)), F.card) =
      (ordinaryFibres (G := G)).card * (twoTorsion : Finset G).card := by
    calc
      (∑ F ∈ (ordinaryFibres (G := G)), F.card) =
          ∑ _F ∈ (ordinaryFibres (G := G)), (twoTorsion : Finset G).card := by
        apply Finset.sum_congr rfl
        intro F hF; exact (Finset.mem_filter.mp hF).2
      _ = _ := by simp
  have hE : (∑ F ∈ (exceptionalFibres (G := G)), F.card) =
      (exceptionalFibres (G := G)).card * (2 * (twoTorsion : Finset G).card) := by
    calc
      (∑ F ∈ (exceptionalFibres (G := G)), F.card) =
          ∑ _F ∈ (exceptionalFibres (G := G)), 2 * (twoTorsion : Finset G).card := by
        apply Finset.sum_congr rfl
        intro F hF; exact exceptionalFibres_member_card F hF
      _ = _ := by simp
  rw [hO, hE] at hc
  rw [hc, Nat.mul_add]
  ac_rfl





end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (Nat.choose (@Fintype.card.{p2m_u_0} G inst_2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Couret.STROBO2TORS.exceptionalFibres.{p2m_u_0} G inst inst_1 inst_2))))) := @_root_.Couret.STROBO2TORS.p2m_local_tripleSupports_weighted_card

