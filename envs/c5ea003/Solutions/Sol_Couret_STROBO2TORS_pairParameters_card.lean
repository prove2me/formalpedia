-- Prove2me | solution 1 for Couret.STROBO2TORS.pairParameters_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:07.577594+00:00
-- url     : https://prove2.me/submissions/1e564b86-ac3c-4e79-b6df-65889bcaf90d

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_pairLifts_card_balance
import Theorems.Thm_Couret_STROBO2TORS_twoTorsion_card_ge_two
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]













/-- A subtraction-safe fixed-direction count, including h=2. -/
theorem pairLifts_card (d v : G)
    (hd : d+d=0) (hd0 : d ≠ 0) (hv : (v+v)+v=0) (hv0 : v ≠ 0) :
    (pairLifts d v).card =
      Fintype.card G * (twoTorsion : Finset G).card - 6 * (twoTorsion : Finset G).card + 1 := by
  have hb := pairLifts_card_balance d v hd hd0 hv hv0
  have hh := twoTorsion_card_ge_two d hd hd0
  have hn : 6 ≤ Fintype.card G := by nlinarith
  have hbound : 6 * (twoTorsion : Finset G).card ≤
      Fintype.card G * (twoTorsion : Finset G).card := Nat.mul_le_mul_right _ hn
  omega














theorem p2m_local_pairParameters_card :
    (pairParameters : Finset (PairParameter G)).card =
      ((twoTorsion : Finset G).card-1) * ((threeTorsion : Finset G).card-1) *
        (Fintype.card G * (twoTorsion : Finset G).card - 6 * (twoTorsion : Finset G).card + 1) := by
  unfold pairParameters
  rw [Finset.card_sigma]
  calc
    _ = ∑ _dv ∈ (((twoTorsion : Finset G).erase 0) ×ˢ ((threeTorsion : Finset G).erase 0)),
        (Fintype.card G * (twoTorsion : Finset G).card - 6 * (twoTorsion : Finset G).card + 1) := by
      apply Finset.sum_congr rfl
      rintro ⟨d,v⟩ hp
      obtain ⟨hd,hv⟩ := Finset.mem_product.mp hp
      exact pairLifts_card d v ((mem_twoTorsion d).mp (Finset.mem_erase.mp hd).2)
        (Finset.mem_erase.mp hd).1 ((mem_threeTorsion v).mp (Finset.mem_erase.mp hv).2)
        (Finset.mem_erase.mp hv).1
    _ = _ := by
      have h0H : (0:G) ∈ twoTorsion := (mem_twoTorsion _).mpr (by simp)
      have h0T : (0:G) ∈ threeTorsion := (mem_threeTorsion _).mpr (by simp)
      simp [Finset.card_erase_of_mem h0H,Finset.card_erase_of_mem h0T]



attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Couret.STROBO2TORS.PairParameter.{p2m_u_0} G)
      (@Couret.STROBO2TORS.pairParameters.{p2m_u_0} G inst inst_1 inst_2))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_pairParameters_card

