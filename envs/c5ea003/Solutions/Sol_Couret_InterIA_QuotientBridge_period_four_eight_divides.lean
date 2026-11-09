-- Prove2me | solution 1 for Couret.InterIA.QuotientBridge.period_four_eight_divides
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:47.31568+00:00
-- url     : https://prove2.me/submissions/2398e12b-2717-4f25-97b7-c3ab63c188ca

import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.Projection
open Couret.InterIA.NormalForm





/-- The period-four branch alone implies 8|n. -/
theorem p2m_local_period_four_eight_divides (m : ℕ) (hm : 0 < m) (d : ZMod m)
    (hd : addOrderOf d=4) : 8 ∣ 2*m := by
  letI : NeZero m := ⟨by omega⟩
  have h4 : 4 ∣ m := by
    have h := addOrderOf_dvd_card (x := d)
    simpa only [ZMod.card,hd] using h
  obtain ⟨k,hk⟩ := h4
  exact ⟨k,by omega⟩



end Couret.InterIA.QuotientBridge

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀ (d : ZMod m),
      @Eq.{1} Nat
          (@addOrderOf.{0} (ZMod m)
            (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                (@Ring.toAddGroupWithOne.{0} (ZMod m) (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))
            d)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) := @_root_.Couret.InterIA.QuotientBridge.p2m_local_period_four_eight_divides

