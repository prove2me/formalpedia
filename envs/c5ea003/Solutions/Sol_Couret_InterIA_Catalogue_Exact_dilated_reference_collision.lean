-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.dilated_reference_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:14:05.138197+00:00
-- url     : https://prove2.me/submissions/b4474c35-5605-4736-bae4-dd7962de6581

import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_scaled_parameter_admissible
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_nonaffine_iff_gcd
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternA_dilate
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternB_dilate
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_admissible_patterns_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternA_card_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_patternB_card_iff
import Definitions.Def_Couret_AmbientCollisionAssembly_e789a884d541

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Arithmetic Couret.InterIA.Catalogue.Quarter.Ambient
open Couret.InterIA.Catalogue.Quarter.AffineCriterion Couret.InterIA.Catalogue.AffineTransport















theorem p2m_local_dilated_reference_collision (n d b : ℕ) (hn : n=4*(d*b))
    (hd : 0 < d) (hb : 0 < b) (hm : b%4=2) :
    FourCollision ((patternA b 1).image (dilate n d))
      ((patternB b 1).image (dilate n d)) := by
  subst n
  have hA := patternA_dilate d b 1 hd
  have hB := patternB_dilate d b 1 hd
  simp only [Nat.cast_one,Nat.mul_one] at hA hB
  rw [hA,hB]
  have hq : 0 < d*b := Nat.mul_pos hd hb
  have hx := scaled_parameter_admissible d b hd (by omega)
  have hlt : d < 4*(d*b) := by
    have hh : d < d*b := by
      simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left (by omega : 1 < b) hd
    omega
  have hg : (d*b).gcd d=d := Nat.gcd_eq_right_iff_dvd.mpr ⟨b,rfl⟩
  have hna : ¬ AffineEquivalent (patternA (d*b) (d : ℕ)) (patternB (d*b) (d : ℕ)) := by
    apply (nonaffine_iff_gcd (d*b) hq d hx).mpr
    rw [ZMod.val_natCast_of_lt hlt,hg,Nat.mul_div_cancel_left b hd]
    exact hm
  exact ⟨(patternA_card_iff (d*b) hq d).mpr hx,(patternB_card_iff (d*b) hq d).mpr hx,
    admissible_patterns_collision (d*b) hq d hx,hna⟩



end Couret.InterIA.Catalogue.Exact

theorem solution : ∀ (n d b : Nat),
  @Eq.{1} Nat n
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)) →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
        @Eq.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) b
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          @Couret.InterIA.Catalogue.Exact.FourCollision n
            (@Finset.image.{0, 0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
              (ZMod n) (ZMod.decidableEq n)
              (@Couret.InterIA.Catalogue.Quarter.Primitive.dilate n d
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
              (Couret.InterIA.Catalogue.Quarter.patternA b
                (@OfNat.ofNat.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                  (nat_lit 1)
                  (@One.toOfNat1.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                    (@AddMonoidWithOne.toOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                          (@CommRing.toRing.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))))))))))
            (@Finset.image.{0, 0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
              (ZMod n) (ZMod.decidableEq n)
              (@Couret.InterIA.Catalogue.Quarter.Primitive.dilate n d
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
              (Couret.InterIA.Catalogue.Quarter.patternB b
                (@OfNat.ofNat.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                  (nat_lit 1)
                  (@One.toOfNat1.{0}
                    (ZMod
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                    (@AddMonoidWithOne.toOne.{0}
                      (ZMod
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                      (@AddGroupWithOne.toAddMonoidWithOne.{0}
                        (ZMod
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                          (@CommRing.toRing.{0}
                            (ZMod
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b))
                            (ZMod.commRing
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b)))))))))) := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_dilated_reference_collision

