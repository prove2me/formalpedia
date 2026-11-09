-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeFullFibres_reduced_size_exists
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:17.063899+00:00
-- url     : https://prove2.me/submissions/0a26d4cb-5612-4f71-91c2-23dd5de132d7

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeExceptionalFibres_reduced_card
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeFullFibres_eq_union
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]







/-- Nontrivial two-torsion and three-torsion force the reduced exceptional
size 2h-2 to occur, even when this size equals an ordinary fibre size. -/
theorem p2m_local_zeroFreeFullFibres_reduced_size_exists
    (hh : 1 < (twoTorsion : Finset G).card)
    (ht : 1 < (threeTorsion : Finset G).card) :
    ∃ F : Finset (Finset G),
      F ∈ (zeroFreeFullFibres : Finset (Finset (Finset G))) ∧
      F.card = 2 * (twoTorsion : Finset G).card - 2 := by
  have hPairs : 0 < (threeSignPairs : Finset (Finset G)).card := by
    have hCount := threeTorsion_nonzero_card_eq_two_pairs (G := G)
    omega
  have hPos :
      0 < (((zeroFreeExceptionalFibres : Finset (Finset (Finset G))).filter
        (fun F => F.card = 2 * (twoTorsion : Finset G).card - 2)).card) := by
    rw [zeroFreeExceptionalFibres_reduced_card]
    have hH : 0 < (twoTorsion : Finset G).card - 1 := by omega
    exact Nat.mul_pos (Nat.mul_pos (by omega) hH) hPairs
  obtain ⟨F, hF⟩ := Finset.card_pos.mp hPos
  obtain ⟨hExc, hCard⟩ := Finset.mem_filter.mp hF
  refine ⟨F, ?_, hCard⟩
  rw [zeroFreeFullFibres_eq_union]
  exact Finset.mem_union.mpr (Or.inr hExc)




















end Finite
end Couret.STROBO2TORS





universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2)) →
      @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) fun F =>
        And
          (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)))
              (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))))
            (@Couret.STROBO2TORS.zeroFreeFullFibres.{p2m_u_0} G inst inst_1 inst_2) F)
          (@Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeFullFibres_reduced_size_exists

