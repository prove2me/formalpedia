-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.c4_square_embedding_product_factor
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:51:26.687676+00:00
-- url     : https://prove2.me/submissions/83326f58-828c-4ed6-942e-a5d3352bd279

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
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
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.AbelianBoundary Couret.InterIA.Parity
variable {P H : Type*} [AddCommGroup P] [AddCommGroup H]

theorem source_four_torsion : ∀ z : G4, (4:ℕ) • z=0 := by decide



theorem p2m_local_c4_square_embedding_product_factor
    (hH : ∀ y : H, (4:ℕ) • y=0 → y=0)
    (φ : G4 →+ P × H) (hφ : Function.Injective φ) :
    ∃ ψ : G4 →+ P, Function.Injective ψ := by
  let ψ : G4 →+ P :=
    { toFun := fun z => (φ z).1
      map_zero' := by simpa using congrArg Prod.fst φ.map_zero
      map_add' := fun a b => by simpa using congrArg Prod.fst (φ.map_add a b) }
  have hz : ∀ z, (φ z).2=0 := by
    intro z
    apply hH
    calc
      (4:ℕ) • (φ z).2=(φ ((4:ℕ) • z)).2 := by
        simpa using (congrArg Prod.snd (map_nsmul φ 4 z)).symm
      _ = 0 := by rw [source_four_torsion,map_zero]; rfl
  refine ⟨ψ,?_⟩
  intro a b hab
  apply hφ
  exact Prod.ext hab (by rw [hz,hz])







end Couret.InterIA.SingletonNecessity

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {P : Type p2m_u_0} {H : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} P] [inst_1 : AddCommGroup.{p2m_u_1} H],
  (∀ (y : H),
      @Eq.{p2m_u_1 + 1} H
          (@HSMul.hSMul.{0, p2m_u_1, p2m_u_1} Nat H H
            (@instHSMul.{0, p2m_u_1} Nat H
              (@AddMonoid.toNSMul.{p2m_u_1} H
                (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                  (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) y)
          (@OfNat.ofNat.{p2m_u_1} H (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_1} H
              (@NegZeroClass.toZero.{p2m_u_1} H
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} H
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} H
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} H
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} H inst_1))))))) →
        @Eq.{p2m_u_1 + 1} H y
          (@OfNat.ofNat.{p2m_u_1} H (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_1} H
              (@NegZeroClass.toZero.{p2m_u_1} H
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} H
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} H
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} H
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} H inst_1)))))))) →
    ∀
      (φ :
        @AddMonoidHom.{0, max p2m_u_1 p2m_u_0} Couret.InterIA.AbelianBoundary.G4 (Prod.{p2m_u_0, p2m_u_1} P H)
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
          (@AddZeroClass.toAddZero.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H)
            (@Prod.instAddZeroClass.{p2m_u_0, p2m_u_1} P H
              (@AddMonoid.toAddZeroClass.{p2m_u_0} P
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} P
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} P (@AddCommGroup.toAddGroup.{p2m_u_0} P inst))))
              (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                  (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_1))))))),
      @Function.Injective.{1, max (p2m_u_0 + 1) (p2m_u_1 + 1)} Couret.InterIA.AbelianBoundary.G4
          (Prod.{p2m_u_0, p2m_u_1} P H)
          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), 1, max (p2m_u_0 + 1) (p2m_u_1 + 1)}
            (@AddMonoidHom.{0, max p2m_u_1 p2m_u_0} Couret.InterIA.AbelianBoundary.G4 (Prod.{p2m_u_0, p2m_u_1} P H)
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
              (@AddZeroClass.toAddZero.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H)
                (@Prod.instAddZeroClass.{p2m_u_0, p2m_u_1} P H
                  (@AddMonoid.toAddZeroClass.{p2m_u_0} P
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} P
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} P (@AddCommGroup.toAddGroup.{p2m_u_0} P inst))))
                  (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                    (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                      (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_1)))))))
            Couret.InterIA.AbelianBoundary.G4 (fun x => Prod.{p2m_u_0, p2m_u_1} P H)
            (@AddMonoidHom.instFunLike.{0, max p2m_u_0 p2m_u_1} Couret.InterIA.AbelianBoundary.G4
              (Prod.{p2m_u_0, p2m_u_1} P H)
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
              (@AddZeroClass.toAddZero.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} P H)
                (@Prod.instAddZeroClass.{p2m_u_0, p2m_u_1} P H
                  (@AddMonoid.toAddZeroClass.{p2m_u_0} P
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} P
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} P (@AddCommGroup.toAddGroup.{p2m_u_0} P inst))))
                  (@AddMonoid.toAddZeroClass.{p2m_u_1} H
                    (@SubNegMonoid.toAddMonoid.{p2m_u_1} H
                      (@AddGroup.toSubNegMonoid.{p2m_u_1} H (@AddCommGroup.toAddGroup.{p2m_u_1} H inst_1)))))))
            φ) →
        @Exists.{p2m_u_0 + 1}
          (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 P
            (@AddZeroClass.toAddZero.{0} Couret.InterIA.AbelianBoundary.G4
              (@Prod.instAddZeroClass.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
            (@AddZeroClass.toAddZero.{p2m_u_0} P
              (@AddMonoid.toAddZeroClass.{p2m_u_0} P
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} P
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} P (@AddCommGroup.toAddGroup.{p2m_u_0} P inst))))))
          fun ψ =>
          @Function.Injective.{1, p2m_u_0 + 1} Couret.InterIA.AbelianBoundary.G4 P
            (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
              (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 P
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
                (@AddZeroClass.toAddZero.{p2m_u_0} P
                  (@AddMonoid.toAddZeroClass.{p2m_u_0} P
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} P
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} P (@AddCommGroup.toAddGroup.{p2m_u_0} P inst))))))
              Couret.InterIA.AbelianBoundary.G4 (fun x => P)
              (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 P
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
                (@AddZeroClass.toAddZero.{p2m_u_0} P
                  (@AddMonoid.toAddZeroClass.{p2m_u_0} P
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} P
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} P (@AddCommGroup.toAddGroup.{p2m_u_0} P inst))))))
              ψ) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_c4_square_embedding_product_factor

