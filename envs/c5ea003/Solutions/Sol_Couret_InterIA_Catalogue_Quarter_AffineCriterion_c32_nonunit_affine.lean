-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.AffineCriterion.c32_nonunit_affine
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:34.596064+00:00
-- url     : https://prove2.me/submissions/6d968726-39dc-436c-bbb5-bdfb6eda04bf

import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_iff_four_systems
import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
import Definitions.Def_Couret_QuarterPatterns_d02dd43ea8cd
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.NormalForm







theorem c32_nonunit_positive_certificate :
    FourSystems 8 (2 : ZMod 32) (⟨5,13,by decide,by decide⟩ : (ZMod 32)ˣ) := by
  unfold FourSystems
  decide



theorem p2m_local_c32_nonunit_affine :
    AffineEquivalent (patternA 8 (2 : ZMod 32)) (patternB 8 (2 : ZMod 32)) := by
  exact (affine_iff_four_systems 8 (by decide) 2 (by decide)).mpr
    ⟨_,c32_nonunit_positive_certificate⟩

end Couret.InterIA.Catalogue.Quarter.AffineCriterion

theorem solution : @Couret.InterIA.NormalForm.AffineEquivalent
  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
  (Couret.InterIA.Catalogue.Quarter.patternA (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) (nat_lit 2)
        (@AddMonoidWithOne.toNatCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
          (@AddGroupWithOne.toAddMonoidWithOne.{0}
            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
            (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))))
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  (Couret.InterIA.Catalogue.Quarter.patternB (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) (nat_lit 2)
        (@AddMonoidWithOne.toNatCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
          (@AddGroupWithOne.toAddMonoidWithOne.{0}
            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
            (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))))
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) := @_root_.Couret.InterIA.Catalogue.Quarter.AffineCriterion.p2m_local_c32_nonunit_affine

