-- Prove2me | solution 1 for Couret.InterIA.QuotientBridge.even_L4_four_divides_order
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:57:31.03089+00:00
-- url     : https://prove2.me/submissions/d9cd20c8-8c00-4b19-b0c8-7a570dcc4c58

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
import Theorems.Thm_Couret_InterIA_NormalForm_even_cyclic_L4
import Theorems.Thm_Couret_InterIA_QuotientBridge_normal_quotient_period
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.Projection
open Couret.InterIA.NormalForm

/-- Existing even L4 feeds the quotient dichotomy without repeating an intersection proof. -/
theorem even_L4_quotient_orders (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) :
    ∃ t : ZMod (2*m), (t=0 ∨ t=m) ∧
      ∃ a b : ZMod (2*m), S \ T.image (fun x => x+t)=fibre (m : ZMod (2*m)) a ∧
        T.image (fun x => x+t) \ S=fibre (m : ZMod (2*m)) b ∧
        (addOrderOf (projection m (b-a))=2 ∨ addOrderOf (projection m (b-a))=4) := by
  obtain ⟨t,ht,hN⟩ := even_cyclic_L4 m hm S T hS hT hsq hnaff
  have ht2 : t+t=0 := by
    rcases ht with rfl|rfl
    · simp
    · exact Couret.InterIA.L4.half_add_half m
  have hc : ∀ z, orderedSquare S z=orderedSquare (T.image (fun x => x+t)) z := by
    intro z
    rw [Couret.InterIA.Translation.two_torsion_translation_preserves_square T t ht2,hsq z]
  exact ⟨t,ht,normal_quotient_period m hm S _ hN hc⟩

/-- A valid intermediate divisibility result; it does not assert 8|n. -/
theorem p2m_local_even_L4_four_divides_order (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) : 4 ∣ 2*m := by
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨t,_,a,b,_,_,hd⟩ := even_L4_quotient_orders m hm S T hS hT hsq hnaff
  have hcard : addOrderOf (projection m (b-a)) ∣ m := by
    simpa only [ZMod.card] using (addOrderOf_dvd_card (x := projection m (b-a)))
  have h2 : 2 ∣ m := by
    rcases hd with hd|hd
    · rwa [hd] at hcard
    · rw [hd] at hcard
      exact dvd_trans (by decide : 2 ∣ 4) hcard
  obtain ⟨k,hk⟩ := h2
  exact ⟨k,by omega⟩





end Couret.InterIA.QuotientBridge

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (S T :
        Finset.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
      @Eq.{1} Nat
          (@Finset.card.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            S)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @Eq.{1} Nat
            (@Finset.card.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
              T)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          (∀
              (z :
                ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)),
              @Eq.{1} Nat
                (@Couret.InterIA.Parity.orderedSquare.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@Ring.toAddCommGroup.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommRing.toRing.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod.commRing
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
                  (ZMod.decidableEq
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  S z)
                (@Couret.InterIA.Parity.orderedSquare.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  (@Ring.toAddCommGroup.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                    (@CommRing.toRing.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                      (ZMod.commRing
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
                  (ZMod.decidableEq
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
                  T z)) →
            Not
                (@Couret.InterIA.NormalForm.AffineEquivalent
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
                  S T) →
              @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) := @_root_.Couret.InterIA.QuotientBridge.p2m_local_even_L4_four_divides_order

