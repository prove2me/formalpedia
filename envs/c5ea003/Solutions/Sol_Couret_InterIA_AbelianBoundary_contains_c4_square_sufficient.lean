-- Prove2me | solution 1 for Couret.InterIA.AbelianBoundary.contains_c4_square_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:29.280909+00:00
-- url     : https://prove2.me/submissions/1dc0f275-0e3d-4dea-8a15-1bf5a3bd7ec9

import Definitions.Def_Couret_AbelianBoundary_ad32094cf511
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
import Theorems.Thm_Couret_InterIA_AbelianBoundary_common_singleton
import Theorems.Thm_Couret_InterIA_AbelianBoundary_source_card
import Theorems.Thm_Couret_InterIA_AbelianBoundary_square_collision
import Theorems.Thm_Couret_InterIA_AbelianBoundary_target_card
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.AbelianBoundary
open Finset Couret.InterIA.Parity
variable {G H : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [DecidableEq H]

theorem orderedSquare_image_at (f : G →+ H) (hf : Function.Injective f)
    (A : Finset G) (z : G) :
    orderedSquare (A.image f) (f z)=orderedSquare A z := by
  simp only [orderedSquare, Finset.sum_image (fun _ _ _ _ he => hf he),
    ← map_add, hf.eq_iff]

theorem orderedSquare_image_outside (f : G →+ H) (A : Finset G) (z : H)
    (hz : ¬ ∃ x : G, f x=z) : orderedSquare (A.image f) z=0 := by
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
  have hne : f x+f y≠z := by
    intro he
    exact hz ⟨x+y,by simpa only [map_add] using he⟩
  simp only [hne,if_false]

theorem collision_image (f : G →+ H) (hf : Function.Injective f)
    (A B : Finset G) (he : ∀ z, orderedSquare A z=orderedSquare B z) :
    ∀ z, orderedSquare (A.image f) z=orderedSquare (B.image f) z := by
  intro z
  by_cases hz : ∃ x : G, f x=z
  · obtain ⟨x,rfl⟩ := hz
    rw [orderedSquare_image_at f hf A,orderedSquare_image_at f hf B,he]
  · rw [orderedSquare_image_outside f A z hz,orderedSquare_image_outside f B z hz]

/-- A sufficient structural condition, with no enumeration of the ambient group. -/
theorem p2m_local_contains_c4_square_sufficient (f : G4 →+ H) (hf : Function.Injective f) :
    ∃ A B : Finset H, A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      (∀ z, orderedSquare A z=orderedSquare B z) := by
  refine ⟨S.image f,T.image f,?_,?_,?_,collision_image f hf S T square_collision⟩
  · rw [Finset.card_image_of_injective _ hf,source_card]
  · rw [Finset.card_image_of_injective _ hf,target_card]
  · rw [← Finset.image_inter _ _ hf,Finset.card_image_of_injective _ hf,common_singleton]
    simp
end Couret.InterIA.AbelianBoundary

universe p2m_u_0
theorem solution : ∀ {H : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} H] [inst_1 : DecidableEq.{p2m_u_0 + 1} H]
  (f :
    @AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 H
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
      (@AddZeroClass.toAddZero.{p2m_u_0} H
        (@AddMonoid.toAddZeroClass.{p2m_u_0} H
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
            (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst)))))),
  @Function.Injective.{1, p2m_u_0 + 1} Couret.InterIA.AbelianBoundary.G4 H
      (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
        (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 H
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
          (@AddZeroClass.toAddZero.{p2m_u_0} H
            (@AddMonoid.toAddZeroClass.{p2m_u_0} H
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst))))))
        Couret.InterIA.AbelianBoundary.G4 (fun x => H)
        (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 H
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
          (@AddZeroClass.toAddZero.{p2m_u_0} H
            (@AddMonoid.toAddZeroClass.{p2m_u_0} H
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} H
                (@AddGroup.toSubNegMonoid.{p2m_u_0} H (@AddCommGroup.toAddGroup.{p2m_u_0} H inst))))))
        f) →
    @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} H) fun A =>
      @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} H) fun B =>
        And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} H A) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} H B) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (And
              (@Eq.{1} Nat
                (@Finset.card.{p2m_u_0} H
                  (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} H) (@Finset.instInter.{p2m_u_0} H inst_1) A B))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (∀ (z : H),
                @Eq.{1} Nat (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} H inst inst_1 A z)
                  (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} H inst inst_1 B z)))) := @_root_.Couret.InterIA.AbelianBoundary.p2m_local_contains_c4_square_sufficient

