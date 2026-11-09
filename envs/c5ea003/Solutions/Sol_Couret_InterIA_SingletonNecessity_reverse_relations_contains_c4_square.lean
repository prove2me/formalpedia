-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.reverse_relations_contains_c4_square
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:07:08.593047+00:00
-- url     : https://prove2.me/submissions/fe6906b3-dcb2-48a9-8488-33ccd6ed71ff

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_MatchingElimination_8675038abe55
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_distinct_values
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_basis
import Theorems.Thm_Couret_InterIA_SingletonNecessity_reverse_matching_contains_c4_square
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G]



theorem p2m_local_reverse_relations_contains_c4_square (x : Fin 6 → G)
    (hd : DistinctLabels x) (hr : RelationsHold x false reversePerm) :
    ∃ φ : G4 →+ G, Function.Injective φ := by
  have ev0 : evaluation x (basis 0) = x 0 := evaluation_basis x (0:Fin 6)
  have ev1 : evaluation x (basis 1) = x 1 := evaluation_basis x (1:Fin 6)
  have ev2 : evaluation x (basis 2) = x 2 := evaluation_basis x (2:Fin 6)
  have ev3 : evaluation x (basis 3) = x 3 := evaluation_basis x (3:Fin 6)
  have ev4 : evaluation x (basis 4) = x 4 := evaluation_basis x (4:Fin 6)
  have ev5 : evaluation x (basis 5) = x 5 := evaluation_basis x (5:Fin 6)
  have hda : x 0+x 0=x 3+x 3 := by
    have h := hr ((2:ℤ) • (basis 0-basis 3)) (by simp [relations])
    simp only [map_add,map_sub,ev0,ev3,two_zsmul] at h
    exact sub_eq_zero.mp (by calc
      (x 0+x 0)-(x 3+x 3) = (x 0-x 3)+(x 0-x 3) := by abel
      _ = 0 := h)
  have hdb : x 1+x 1=x 4+x 4 := by
    have h := hr ((2:ℤ) • (basis 1-basis 4)) (by simp [relations])
    simp only [map_add,map_sub,ev1,ev4,two_zsmul] at h
    exact sub_eq_zero.mp (by calc
      (x 1+x 1)-(x 4+x 4) = (x 1-x 4)+(x 1-x 4) := by abel
      _ = 0 := h)
  have ha : x 0=x 4+x 5 := by
    have h := hr (basis 0-(basis 4+basis 5)) (by
      simp [relations,leftTerms,rightTerms,reversePerm])
    simpa only [map_sub,map_add,ev0,ev4,
      ev5,sub_eq_zero] using h
  have hab : x 0+x 1=x 5 := by
    have h := hr ((basis 0+basis 1)-basis 5) (by
      simp [relations,leftTerms,rightTerms,reversePerm])
    simpa only [map_sub,map_add,ev0,ev1,
      ev5,sub_eq_zero] using h
  have hac : x 0+x 2=x 4 := by
    have h := hr ((basis 0+basis 2)-basis 4) (by
      simp [relations,leftTerms,rightTerms,reversePerm])
    simpa only [map_sub,map_add,ev0,ev2,
      ev4,sub_eq_zero] using h
  have hbc : x 1+x 2=x 3 := by
    have h := hr ((basis 1+basis 2)-basis 3) (by
      simp [relations,leftTerms,rightTerms,reversePerm])
    simpa only [map_sub,map_add,ev1,ev2,
      ev3,sub_eq_zero] using h
  have hinj := distinct_values x hd
  exact reverse_matching_contains_c4_square (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    ha hab hac hbc hda hdb
    (fun h => (by decide : (0:Fin 6) ≠ 3) (hinj h))
    (fun h => (by decide : (1:Fin 6) ≠ 4) (hinj h))
    (fun h => (by decide : (2:Fin 6) ≠ 5) (hinj h))



end Couret.InterIA.SingletonNecessity


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.DistinctLabels.{p2m_u_0} G inst x →
    @Couret.InterIA.SingletonNecessity.RelationsHold.{p2m_u_0} G inst x Bool.false
        Couret.InterIA.SingletonNecessity.reversePerm →
      @Exists.{p2m_u_0 + 1}
        (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 G
          (@AddZeroClass.toAddZero.{0} Couret.InterIA.AbelianBoundary.G4
            (@Prod.instAddZeroClass.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
              (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddGroupWithOne.toAddMonoidWithOne.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
          (@AddZeroClass.toAddZero.{p2m_u_0} G
            (@AddMonoid.toAddZeroClass.{p2m_u_0} G
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
        fun φ =>
        @Function.Injective.{1, p2m_u_0 + 1} Couret.InterIA.AbelianBoundary.G4 G
          (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
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
            Couret.InterIA.AbelianBoundary.G4 (fun x => G)
            (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 G
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
            φ) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_reverse_relations_contains_c4_square

