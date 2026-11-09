-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.cross_count_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:18.627853+00:00
-- url     : https://prove2.me/submissions/7175b40a-e674-42b9-b909-a9901f95eda8

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_square_supportLeft
import Theorems.Thm_Couret_InterIA_SingletonNecessity_square_supportRight
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem p2m_local_cross_count_cancellation (x : Fin 6 → G) (hd : SevenDistinct x)
    (hx : CrossDoubles x)
    (hs : ∀ z, orderedSquare (supportLeft x) z=orderedSquare (supportRight x) z) :
    (sumTermsLeft x).Perm (sumTermsRight x) := by
  apply List.perm_iff_count.mpr
  intro z
  have h := hs z
  rw [square_supportLeft x hd,square_supportRight x hd] at h
  rcases hx with ⟨h0,h1,h2⟩
  rw [h0,h1,h2] at h
  omega



end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst x →
    @Couret.InterIA.SingletonNecessity.CrossDoubles.{p2m_u_0} G inst x →
      (∀ (z : G),
          @Eq.{1} Nat
            (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
              (@Couret.InterIA.SingletonNecessity.supportLeft.{p2m_u_0} G inst inst_1 x) z)
            (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
              (@Couret.InterIA.SingletonNecessity.supportRight.{p2m_u_0} G inst inst_1 x) z)) →
        @List.Perm.{p2m_u_0} G (@Couret.InterIA.SingletonNecessity.sumTermsLeft.{p2m_u_0} G inst x)
          (@Couret.InterIA.SingletonNecessity.sumTermsRight.{p2m_u_0} G inst x) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_cross_count_cancellation

