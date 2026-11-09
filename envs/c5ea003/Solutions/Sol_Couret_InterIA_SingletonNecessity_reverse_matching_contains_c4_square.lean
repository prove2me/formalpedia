-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.reverse_matching_contains_c4_square
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:00:37.039207+00:00
-- url     : https://prove2.me/submissions/4e632480-76b8-436c-a76b-0e654f3d7187

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
import Theorems.Thm_Couret_InterIA_AbelianBoundary_double_equals_opposite_double
import Theorems.Thm_Couret_InterIA_SingletonNecessity_contains_c4_square_of_four_torsion
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]













theorem p2m_local_reverse_matching_contains_c4_square (a b c d e f : G)
    (ha : a = e+f) (hab : a+b = f) (hac : a+c = e) (hbc : b+c = d)
    (hda : a+a = d+d) (hdb : b+b = e+e)
    (had : a ≠ d) (hbe : b ≠ e) (hcf : c ≠ f) :
    ∃ φ : G4 →+ G, Function.Injective φ := by
  have hs : a+b+c=0 := by
    calc
      a+b+c = ((a+c)+(a+b))-a := by abel
      _ = (e+f)-a := by rw [hac,hab]
      _ = 0 := by rw [← ha,sub_self]
  have hd : d = -a := by
    calc d = (a+b+c)-a := by rw [← hbc]; abel
         _ = -a := by rw [hs]; simp
  have he : e = -b := by
    calc e = (a+b+c)-b := by rw [← hac]; abel
         _ = -b := by rw [hs]; simp
  have hf : f = -c := by
    calc f = (a+b+c)-c := by rw [← hab]; abel
         _ = -c := by rw [hs]; simp
  have ha4 : (4:ℤ) • a = 0 := by
    have h := double_equals_opposite_double a d hd hda
    simpa only [show (4:ℤ) = 2+2 from rfl,add_zsmul,two_zsmul] using h
  have hb4 : (4:ℤ) • b = 0 := by
    have h := double_equals_opposite_double b e he hdb
    simpa only [show (4:ℤ) = 2+2 from rfl,add_zsmul,two_zsmul] using h
  have ha2 : a+a ≠ 0 := by
    intro h
    apply had
    rw [hd]
    exact eq_neg_iff_add_eq_zero.mpr h
  have hb2 : b+b ≠ 0 := by
    intro h
    apply hbe
    rw [he]
    exact eq_neg_iff_add_eq_zero.mpr h
  have hab2 : a+a ≠ b+b := by
    intro h
    have hc2 : c+c = 0 := by
      have hsum : (a+a)+(b+b)+(c+c)=0 := by
        calc (a+a)+(b+b)+(c+c) = (a+b+c)+(a+b+c) := by abel
             _ = 0 := by rw [hs,zero_add]
      rw [← h] at hsum
      have hzero : (a+a)+(a+a)=0 :=
        double_equals_opposite_double a d hd hda
      rw [hzero,zero_add] at hsum
      exact hsum
    apply hcf
    rw [hf]
    exact eq_neg_iff_add_eq_zero.mpr hc2
  exact contains_c4_square_of_four_torsion a b ha4 hb4 ha2 hb2 hab2

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] (a b c d e f : G),
  @Eq.{p2m_u_0 + 1} G a
      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
        (@instHAdd.{p2m_u_0} G
          (@AddCommMagma.toAdd.{p2m_u_0} G
            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
        e f) →
    @Eq.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          a b)
        f →
      @Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            a c)
          e →
        @Eq.{p2m_u_0 + 1} G
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              b c)
            d →
          @Eq.{p2m_u_0 + 1} G
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
                d d) →
            @Eq.{p2m_u_0 + 1} G
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  b b)
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  e e) →
              @Ne.{p2m_u_0 + 1} G a d →
                @Ne.{p2m_u_0 + 1} G b e →
                  @Ne.{p2m_u_0 + 1} G c f →
                    @Exists.{p2m_u_0 + 1}
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
                                      (ZMod.commRing
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
                        (@AddZeroClass.toAddZero.{p2m_u_0} G
                          (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                      fun φ =>
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
                                          (ZMod.commRing
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
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
                                          (ZMod.commRing
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
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
                                          (ZMod.commRing
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
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
                                          (ZMod.commRing
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                          φ) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_reverse_matching_contains_c4_square

