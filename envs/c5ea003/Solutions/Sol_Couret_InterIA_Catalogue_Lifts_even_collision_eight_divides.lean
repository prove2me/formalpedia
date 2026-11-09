-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Lifts.even_collision_eight_divides
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:03:08.182596+00:00
-- url     : https://prove2.me/submissions/a1a702c6-bedd-4392-b945-e66f9ba5c768

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
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
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_two_lift_affine
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_two_orbit_lift
import Theorems.Thm_Couret_InterIA_Catalogue_Orbits_collision_orbit_shapes
import Theorems.Thm_Couret_InterIA_QuotientBridge_even_L4_four_divides_order
import Theorems.Thm_Couret_InterIA_QuotientBridge_period_four_eight_divides
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Orbits
open Couret.InterIA.Parity

theorem affine_target_untranslate {n : ℕ} (S T : Finset (ZMod n)) (t : ZMod n)
    (h : AffineEquivalent S (T.image (fun x => x+t))) : AffineEquivalent S T := by
  obtain ⟨u,v,he⟩ := h
  refine ⟨u,v-t,?_⟩
  calc S.image (fun x => (u : ZMod n)*x+(v-t)) =
        (S.image (fun x => (u : ZMod n)*x+v)).image (fun x => x-t) := by
          rw [image_image]
          congr 1
          funext x
          dsimp
          abel
       _=T := by rw [he,image_image]; simp only [Function.comp_def,add_sub_cancel_right,Finset.image_id']

/-- Closing the period-two obstruction using the retained geometric witnesses. -/
theorem p2m_local_even_collision_eight_divides (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) : 8 ∣ 2*m := by
  have hfour := Couret.InterIA.QuotientBridge.even_L4_four_divides_order m hm S T hS hT hsq hnaff
  have hmEven : m%2=0 := by obtain ⟨k,hk⟩ := hfour; omega
  by_cases h4 : 4 ∣ m
  · obtain ⟨k,hk⟩ := h4
    exact ⟨k,by omega⟩
  · have hmod : m%4=2 := by
      have hn := Nat.mod_lt m (by decide : 0<4)
      have hz : m%4≠0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using h4
      omega
    obtain ⟨t,ht,ho⟩ := collision_orbit_shapes m hm S T hS hT hsq hnaff
    obtain ⟨a,b,c,d,hU,hV,hcd,hC,hca,hcb,hda,hdb,hshape⟩ := ho
    rcases hshape with ⟨h2,hd⟩|⟨hord,_⟩
    · have hl := two_orbit_lift m hm S (T.image (fun x => x+t)) a b c d hU hV hC h2 hd
      exact False.elim (hnaff (affine_target_untranslate S T t (two_lift_affine m hm hmod S _ hl)))
    · have he := Couret.InterIA.QuotientBridge.period_four_eight_divides m hm _ hord
      obtain ⟨k,hk⟩ := he
      omega



end Couret.InterIA.Catalogue.Lifts

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
              @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m) := @_root_.Couret.InterIA.Catalogue.Lifts.p2m_local_even_collision_eight_divides

