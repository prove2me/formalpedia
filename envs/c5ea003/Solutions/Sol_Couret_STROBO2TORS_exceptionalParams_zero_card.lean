-- Prove2me | solution 1 for Couret.STROBO2TORS.exceptionalParams_zero_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:44.492205+00:00
-- url     : https://prove2.me/submissions/c11d4efa-aeb6-47e4-83dc-577931bbc8d2

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_zero_lifts_card
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]































theorem p2m_local_exceptionalParams_zero_card :
    ((exceptionalParams : Finset ((G × G) × G)).filter
      (fun p => 0 ∈ paramSupport p)).card =
      3 * ((twoTorsion : Finset G).card - 1) * ((threeTorsion : Finset G).card - 1) := by
  have hc : ((exceptionalParams : Finset ((G × G) × G)).filter
      (fun p => 0 ∈ paramSupport p)).card =
      ∑ v ∈ ((threeTorsion : Finset G).erase 0),
        ∑ d ∈ ((twoTorsion : Finset G).erase 0),
          ((Finset.univ : Finset G).filter (fun a => 0 ∈ paramSupport ((a, d), v))).card := by
    calc
      ((exceptionalParams : Finset ((G × G) × G)).filter
          (fun p => 0 ∈ paramSupport p)).card =
          ∑ p ∈ ((Finset.univ : Finset G).product ((twoTorsion : Finset G).erase 0)).product
            ((threeTorsion : Finset G).erase 0), if 0 ∈ paramSupport p then 1 else 0 := by
        simp only [exceptionalParams, Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ v ∈ ((threeTorsion : Finset G).erase 0),
          ∑ p ∈ (Finset.univ : Finset G).product ((twoTorsion : Finset G).erase 0),
            if 0 ∈ paramSupport (p, v) then 1 else 0 :=
        Finset.sum_product_right _ _ _
      _ = ∑ v ∈ ((threeTorsion : Finset G).erase 0),
          ∑ d ∈ ((twoTorsion : Finset G).erase 0),
            ∑ a ∈ (Finset.univ : Finset G), if 0 ∈ paramSupport ((a, d), v) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        exact Finset.sum_product_right _ _ _
      _ = _ := by simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsum : (∑ v ∈ ((threeTorsion : Finset G).erase 0),
        ∑ d ∈ ((twoTorsion : Finset G).erase 0),
          ((Finset.univ : Finset G).filter (fun a => 0 ∈ paramSupport ((a, d), v))).card) =
      ∑ _v ∈ ((threeTorsion : Finset G).erase 0),
        ∑ _d ∈ ((twoTorsion : Finset G).erase 0), 3 := by
    apply Finset.sum_congr rfl
    intro v hv
    obtain ⟨hv0, hv⟩ := Finset.mem_erase.mp hv
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd0, hd⟩ := Finset.mem_erase.mp hd
    exact paramSupport_zero_lifts_card d v ((mem_twoTorsion d).mp hd) hd0
      ((mem_threeTorsion v).mp hv) hv0
  rw [hc, hsum]
  have h0H : (0 : G) ∈ twoTorsion := (mem_twoTorsion 0).mpr (by simp)
  have h0K : (0 : G) ∈ threeTorsion := (mem_threeTorsion 0).mpr (by simp)
  simp only [Finset.sum_const, Finset.card_erase_of_mem h0H,
    Finset.card_erase_of_mem h0K]
  simp only [Nat.nsmul_eq_mul]
  ac_rfl















































end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G)
      (@Finset.filter.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G)
        (fun p =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G))
            (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1 p)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
        (fun a =>
          @Finset.decidableMem.{p2m_u_0} G inst_1
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))
            (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1 a))
        (@Couret.STROBO2TORS.exceptionalParams.{p2m_u_0} G inst inst_1 inst_2)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_exceptionalParams_zero_card

