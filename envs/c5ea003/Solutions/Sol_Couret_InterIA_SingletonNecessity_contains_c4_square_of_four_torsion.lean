-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.contains_c4_square_of_four_torsion
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:04.595791+00:00
-- url     : https://prove2.me/submissions/502caa33-ba8c-42e0-8301-3d9e3b682179

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_injective_of_double_images
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]



theorem fourthMap_two (a : G) (ha : (4:ℤ) • a = 0) :
    fourthMap a ha 2 = a+a := by
  change ZMod.lift 4 _ ((2:ℤ) : ZMod 4) = a+a
  rw [ZMod.lift_coe]
  exact two_zsmul a

theorem fourthMap_zero (a : G) (ha : (4:ℤ) • a = 0) :
    fourthMap a ha 0 = 0 := map_zero _





theorem p2m_local_contains_c4_square_of_four_torsion (a b : G)
    (ha : (4:ℤ) • a = 0) (hb : (4:ℤ) • b = 0)
    (ha2 : a+a ≠ 0) (hb2 : b+b ≠ 0) (hab2 : a+a ≠ b+b) :
    ∃ f : G4 →+ G, Function.Injective f := by
  let f := (fourthMap a ha).coprod (fourthMap b hb)
  have hfa : f (2,0) = a+a := by
    change fourthMap a ha 2 + fourthMap b hb 0 = a+a
    rw [fourthMap_two,fourthMap_zero,add_zero]
  have hfb : f (0,2) = b+b := by
    change fourthMap a ha 0 + fourthMap b hb 2 = b+b
    rw [fourthMap_zero,fourthMap_two,zero_add]
  refine ⟨f, injective_of_double_images f ?_ ?_ ?_⟩
  · rwa [hfa]
  · rwa [hfb]
  · rwa [hfa,hfb]



end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] (a b : G),
  @Eq.{p2m_u_0 + 1} G
      (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Int G G
        (@instHSMul.{0, p2m_u_0} Int G
          (@SubNegMonoid.toZSMul.{p2m_u_0} G
            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) a)
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Eq.{p2m_u_0 + 1} G
        (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Int G G
          (@instHSMul.{0, p2m_u_0} Int G
            (@SubNegMonoid.toZSMul.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) b)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Ne.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            a a)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Ne.{p2m_u_0 + 1} G
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              b b)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          @Ne.{p2m_u_0 + 1} G
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                a a)
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                b b) →
            @Exists.{p2m_u_0 + 1}
              (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 G
                (@AddZeroClass.toAddZero.{0} Couret.InterIA.AbelianBoundary.G4
                  (@Prod.instAddZeroClass.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                            (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
                    (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@AddMonoidWithOne.toAddMonoid.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (@Ring.toAddGroupWithOne.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                            (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
                (@AddZeroClass.toAddZero.{p2m_u_0} G
                  (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
              fun f =>
              @Function.Injective.{1, p2m_u_0 + 1} Couret.InterIA.AbelianBoundary.G4 G
                (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
                  (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 G
                    (@AddZeroClass.toAddZero.{0} Couret.InterIA.AbelianBoundary.G4
                      (@Prod.instAddZeroClass.{0, 0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@AddMonoid.toAddZeroClass.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (@AddMonoidWithOne.toAddMonoid.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (@Ring.toAddGroupWithOne.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                (@CommRing.toRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
                        (@AddMonoid.toAddZeroClass.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (@AddMonoidWithOne.toAddMonoid.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (@Ring.toAddGroupWithOne.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                (@CommRing.toRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
                    (@AddZeroClass.toAddZero.{p2m_u_0} G
                      (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                  Couret.InterIA.AbelianBoundary.G4 (fun x => G)
                  (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 G
                    (@AddZeroClass.toAddZero.{0} Couret.InterIA.AbelianBoundary.G4
                      (@Prod.instAddZeroClass.{0, 0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@AddMonoid.toAddZeroClass.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (@AddMonoidWithOne.toAddMonoid.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (@Ring.toAddGroupWithOne.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                (@CommRing.toRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
                        (@AddMonoid.toAddZeroClass.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (@AddMonoidWithOne.toAddMonoid.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                            (@AddGroupWithOne.toAddMonoidWithOne.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                              (@Ring.toAddGroupWithOne.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                (@CommRing.toRing.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
                    (@AddZeroClass.toAddZero.{p2m_u_0} G
                      (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                  f) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_contains_c4_square_of_four_torsion

